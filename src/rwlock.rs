// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use parking_lot::{
    lock_api::{
        RawRwLock as _,
        RawRwLockFair as _,
        RawRwLockDowngrade as _,
        RawRwLockTimed as _,
        RawRwLockRecursive as _,
        RawRwLockRecursiveTimed as _,
        RawRwLockUpgrade as _,
        RawRwLockUpgradeFair as _,
        RawRwLockUpgradeDowngrade as _,
        RawRwLockUpgradeTimed as _
    },
    RawRwLock,
};
use core::cell::UnsafeCell;
use core::fmt;
use core::marker::PhantomData;
use core::mem;
use core::time::Duration;
use core::ops::{Deref, DerefMut};
use std::time::Instant;

#[cfg(feature = "owning_ref_support")]
use owning_ref::StableAddress;

#[cfg(feature = "serde_support")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// A reader-writer lock
///
/// This type of lock allows a number of readers or at most one writer at any
/// point in time. The write portion of this lock typically allows modification
/// of the underlying data (exclusive access) and the read portion of this lock
/// typically allows for read-only access (shared access).
///
/// The type parameter `T` represents the data that this lock protects. It is
/// required that `T` satisfies `Send` to be shared across threads and `Sync` to
/// allow concurrent access through readers. The RAII guards returned from the
/// locking methods implement `Deref` (and `DerefMut` for the `write` methods)
/// to allow access to the contained of the lock.
pub struct RwLock<T: ?Sized> {
    raw: RawRwLock,
    data: UnsafeCell<T>,
}

// Copied and modified from serde
#[cfg(feature = "serde_support")]
impl<T> Serialize for RwLock<T>
where
    T: Serialize + ?Sized,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.read().serialize(serializer)
    }
}

#[cfg(feature = "serde_support")]
impl<'de, T> Deserialize<'de> for RwLock<T>
where
    T: Deserialize<'de> + ?Sized,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Deserialize::deserialize(deserializer).map(RwLock::new)
    }
}

unsafe impl<T: ?Sized + Send> Send for RwLock<T> {}
unsafe impl<T: ?Sized + Send + Sync> Sync for RwLock<T> {}

impl<T> RwLock<T> {
    /// Creates a new instance of an `RwLock<T>` which is unlocked.
    #[inline]
    pub const fn new(val: T) -> RwLock<T> {
        RwLock {
            data: UnsafeCell::new(val),
            raw: RawRwLock::INIT,
        }
    }

    /// Consumes this `RwLock`, returning the underlying data.
    #[inline]
    #[allow(unused_unsafe)]
    pub fn into_inner(self) -> T {
        unsafe { self.data.into_inner() }
    }
}

impl<T: ?Sized> RwLock<T> {
    /// # Safety
    ///
    /// The lock must be held when calling this method.
    #[inline]
    unsafe fn read_guard(&self) -> RwLockReadGuard<'_, T> {
        RwLockReadGuard {
            rwlock: self,
            marker: PhantomData,
        }
    }

    /// # Safety
    ///
    /// The lock must be held when calling this method.
    #[inline]
    unsafe fn write_guard(&self) -> RwLockWriteGuard<'_, T> {
        RwLockWriteGuard {
            rwlock: self,
            marker: PhantomData,
        }
    }

    /// Locks this `RwLock` with shared read access, blocking the current thread
    /// until it can be acquired.
    ///
    /// The calling thread will be blocked until there are no more writers which
    /// hold the lock. There may be other readers currently inside the lock when
    /// this method returns.
    ///
    /// Note that attempts to recursively acquire a read lock on a `RwLock` when
    /// the current thread already holds one may result in a deadlock.
    ///
    /// Returns an RAII guard which will release this thread's shared access
    /// once it is dropped.
    #[inline]
    pub fn read(&self) -> RwLockReadGuard<'_, T> {
        self.raw.lock_shared();
        // SAFETY: The lock is held, as required.
        unsafe { self.read_guard() }
    }

    /// Attempts to acquire this `RwLock` with shared read access.
    ///
    /// If the access could not be granted at this time, then `None` is returned.
    /// Otherwise, an RAII guard is returned which will release the shared access
    /// when it is dropped.
    ///
    /// This function does not block.
    #[inline]
    pub fn try_read(&self) -> Option<RwLockReadGuard<'_, T>> {
        if self.raw.try_lock_shared() {
            // SAFETY: The lock is held, as required.
            Some(unsafe { self.read_guard() })
        } else {
            None
        }
    }

    /// Locks this `RwLock` with exclusive write access, blocking the current
    /// thread until it can be acquired.
    ///
    /// This function will not return while other writers or other readers
    /// currently have access to the lock.
    ///
    /// Returns an RAII guard which will drop the write access of this `RwLock`
    /// when dropped.
    #[inline]
    pub fn write(&self) -> RwLockWriteGuard<'_, T> {
        self.raw.lock_exclusive();
        // SAFETY: The lock is held, as required.
        unsafe { self.write_guard() }
    }

    /// Attempts to lock this `RwLock` with exclusive write access.
    ///
    /// If the lock could not be acquired at this time, then `None` is returned.
    /// Otherwise, an RAII guard is returned which will release the lock when
    /// it is dropped.
    ///
    /// This function does not block.
    #[inline]
    pub fn try_write(&self) -> Option<RwLockWriteGuard<'_, T>> {
        if self.raw.try_lock_exclusive() {
            // SAFETY: The lock is held, as required.
            Some(unsafe { self.write_guard() })
        } else {
            None
        }
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the `RwLock` mutably, no actual locking needs to
    /// take place---the mutable borrow statically guarantees no locks exist.
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        unsafe { &mut *self.data.get() }
    }

    /// Forcibly unlocks a read lock.
    ///
    /// This is useful when combined with `mem::forget` to hold a lock without
    /// the need to maintain a `RwLockReadGuard` object alive, for example when
    /// dealing with FFI.
    ///
    /// # Safety
    ///
    /// This method must only be called if the current thread logically owns a
    /// `RwLockReadGuard` but that guard has be discarded using `mem::forget`.
    /// Behavior is undefined if a rwlock is read-unlocked when not read-locked.
    #[inline]
    pub unsafe fn force_unlock_read(&self) {
        self.raw.unlock_shared();
    }

    /// Forcibly unlocks a write lock.
    ///
    /// This is useful when combined with `mem::forget` to hold a lock without
    /// the need to maintain a `RwLockWriteGuard` object alive, for example when
    /// dealing with FFI.
    ///
    /// # Safety
    ///
    /// This method must only be called if the current thread logically owns a
    /// `RwLockWriteGuard` but that guard has be discarded using `mem::forget`.
    /// Behavior is undefined if a rwlock is write-unlocked when not write-locked.
    #[inline]
    pub unsafe fn force_unlock_write(&self) {
        self.raw.unlock_exclusive();
    }

    /// Returns the underlying raw reader-writer lock object.
    ///
    /// Note that you will most likely need to import the `RawRwLock` trait from
    /// `lock_api` to be able to call functions on the raw
    /// reader-writer lock.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it allows unlocking a mutex while
    /// still holding a reference to a lock guard.
    pub unsafe fn raw(&self) -> &RawRwLock {
        &self.raw
    }
}

impl<T: ?Sized> RwLock<T> {
    /// Forcibly unlocks a read lock using a fair unlock procotol.
    ///
    /// This is useful when combined with `mem::forget` to hold a lock without
    /// the need to maintain a `RwLockReadGuard` object alive, for example when
    /// dealing with FFI.
    ///
    /// # Safety
    ///
    /// This method must only be called if the current thread logically owns a
    /// `RwLockReadGuard` but that guard has be discarded using `mem::forget`.
    /// Behavior is undefined if a rwlock is read-unlocked when not read-locked.
    #[inline]
    pub unsafe fn force_unlock_read_fair(&self) {
        self.raw.unlock_shared_fair();
    }

    /// Forcibly unlocks a write lock using a fair unlock procotol.
    ///
    /// This is useful when combined with `mem::forget` to hold a lock without
    /// the need to maintain a `RwLockWriteGuard` object alive, for example when
    /// dealing with FFI.
    ///
    /// # Safety
    ///
    /// This method must only be called if the current thread logically owns a
    /// `RwLockWriteGuard` but that guard has be discarded using `mem::forget`.
    /// Behavior is undefined if a rwlock is write-unlocked when not write-locked.
    #[inline]
    pub unsafe fn force_unlock_write_fair(&self) {
        self.raw.unlock_exclusive_fair();
    }
}

impl<T: ?Sized> RwLock<T> {
    /// Attempts to acquire this `RwLock` with shared read access until a timeout
    /// is reached.
    ///
    /// If the access could not be granted before the timeout expires, then
    /// `None` is returned. Otherwise, an RAII guard is returned which will
    /// release the shared access when it is dropped.
    #[inline]
    pub fn try_read_for(&self, timeout: Duration) -> Option<RwLockReadGuard<'_, T>> {
        if self.raw.try_lock_shared_for(timeout) {
            // SAFETY: The lock is held, as required.
            Some(unsafe { self.read_guard() })
        } else {
            None
        }
    }

    /// Attempts to acquire this `RwLock` with shared read access until a timeout
    /// is reached.
    ///
    /// If the access could not be granted before the timeout expires, then
    /// `None` is returned. Otherwise, an RAII guard is returned which will
    /// release the shared access when it is dropped.
    #[inline]
    pub fn try_read_until(&self, timeout: Instant) -> Option<RwLockReadGuard<'_, T>> {
        if self.raw.try_lock_shared_until(timeout) {
            // SAFETY: The lock is held, as required.
            Some(unsafe { self.read_guard() })
        } else {
            None
        }
    }

    /// Attempts to acquire this `RwLock` with exclusive write access until a
    /// timeout is reached.
    ///
    /// If the access could not be granted before the timeout expires, then
    /// `None` is returned. Otherwise, an RAII guard is returned which will
    /// release the exclusive access when it is dropped.
    #[inline]
    pub fn try_write_for(&self, timeout: Duration) -> Option<RwLockWriteGuard<'_, T>> {
        if self.raw.try_lock_exclusive_for(timeout) {
            // SAFETY: The lock is held, as required.
            Some(unsafe { self.write_guard() })
        } else {
            None
        }
    }

    /// Attempts to acquire this `RwLock` with exclusive write access until a
    /// timeout is reached.
    ///
    /// If the access could not be granted before the timeout expires, then
    /// `None` is returned. Otherwise, an RAII guard is returned which will
    /// release the exclusive access when it is dropped.
    #[inline]
    pub fn try_write_until(&self, timeout: Instant) -> Option<RwLockWriteGuard<'_, T>> {
        if self.raw.try_lock_exclusive_until(timeout) {
            // SAFETY: The lock is held, as required.
            Some(unsafe { self.write_guard() })
        } else {
            None
        }
    }
}

impl<T: ?Sized> RwLock<T> {
    /// Locks this `RwLock` with shared read access, blocking the current thread
    /// until it can be acquired.
    ///
    /// The calling thread will be blocked until there are no more writers which
    /// hold the lock. There may be other readers currently inside the lock when
    /// this method returns.
    ///
    /// Unlike `read`, this method is guaranteed to succeed without blocking if
    /// another read lock is held at the time of the call. This allows a thread
    /// to recursively lock a `RwLock`. However using this method can cause
    /// writers to starve since readers no longer block if a writer is waiting
    /// for the lock.
    ///
    /// Returns an RAII guard which will release this thread's shared access
    /// once it is dropped.
    #[inline]
    pub fn read_recursive(&self) -> RwLockReadGuard<'_, T> {
        self.raw.lock_shared_recursive();
        // SAFETY: The lock is held, as required.
        unsafe { self.read_guard() }
    }

    /// Attempts to acquire this `RwLock` with shared read access.
    ///
    /// If the access could not be granted at this time, then `None` is returned.
    /// Otherwise, an RAII guard is returned which will release the shared access
    /// when it is dropped.
    ///
    /// This method is guaranteed to succeed if another read lock is held at the
    /// time of the call. See the documentation for `read_recursive` for details.
    ///
    /// This function does not block.
    #[inline]
    pub fn try_read_recursive(&self) -> Option<RwLockReadGuard<'_, T>> {
        if self.raw.try_lock_shared_recursive() {
            // SAFETY: The lock is held, as required.
            Some(unsafe { self.read_guard() })
        } else {
            None
        }
    }
}

impl<T: ?Sized> RwLock<T> {
    /// Attempts to acquire this `RwLock` with shared read access until a timeout
    /// is reached.
    ///
    /// If the access could not be granted before the timeout expires, then
    /// `None` is returned. Otherwise, an RAII guard is returned which will
    /// release the shared access when it is dropped.
    ///
    /// This method is guaranteed to succeed without blocking if another read
    /// lock is held at the time of the call. See the documentation for
    /// `read_recursive` for details.
    #[inline]
    pub fn try_read_recursive_for(
        &self,
        timeout: Duration,
    ) -> Option<RwLockReadGuard<'_, T>> {
        if self.raw.try_lock_shared_recursive_for(timeout) {
            // SAFETY: The lock is held, as required.
            Some(unsafe { self.read_guard() })
        } else {
            None
        }
    }

    /// Attempts to acquire this `RwLock` with shared read access until a timeout
    /// is reached.
    ///
    /// If the access could not be granted before the timeout expires, then
    /// `None` is returned. Otherwise, an RAII guard is returned which will
    /// release the shared access when it is dropped.
    #[inline]
    pub fn try_read_recursive_until(
        &self,
        timeout: Instant,
    ) -> Option<RwLockReadGuard<'_, T>> {
        if self.raw.try_lock_shared_recursive_until(timeout) {
            // SAFETY: The lock is held, as required.
            Some(unsafe { self.read_guard() })
        } else {
            None
        }
    }
}

impl<T: ?Sized> RwLock<T> {
    /// # Safety
    ///
    /// The lock must be held when calling this method.
    #[inline]
    unsafe fn upgradable_guard(&self) -> RwLockUpgradableReadGuard<'_, T> {
        RwLockUpgradableReadGuard {
            rwlock: self,
            marker: PhantomData,
        }
    }

    /// Locks this `RwLock` with upgradable read access, blocking the current thread
    /// until it can be acquired.
    ///
    /// The calling thread will be blocked until there are no more writers or other
    /// upgradable reads which hold the lock. There may be other readers currently
    /// inside the lock when this method returns.
    ///
    /// Returns an RAII guard which will release this thread's shared access
    /// once it is dropped.
    #[inline]
    pub fn upgradable_read(&self) -> RwLockUpgradableReadGuard<'_, T> {
        self.raw.lock_upgradable();
        // SAFETY: The lock is held, as required.
        unsafe { self.upgradable_guard() }
    }

    /// Attempts to acquire this `RwLock` with upgradable read access.
    ///
    /// If the access could not be granted at this time, then `None` is returned.
    /// Otherwise, an RAII guard is returned which will release the shared access
    /// when it is dropped.
    ///
    /// This function does not block.
    #[inline]
    pub fn try_upgradable_read(&self) -> Option<RwLockUpgradableReadGuard<'_, T>> {
        if self.raw.try_lock_upgradable() {
            // SAFETY: The lock is held, as required.
            Some(unsafe { self.upgradable_guard() })
        } else {
            None
        }
    }
}

impl<T: ?Sized> RwLock<T> {
    /// Attempts to acquire this `RwLock` with upgradable read access until a timeout
    /// is reached.
    ///
    /// If the access could not be granted before the timeout expires, then
    /// `None` is returned. Otherwise, an RAII guard is returned which will
    /// release the shared access when it is dropped.
    #[inline]
    pub fn try_upgradable_read_for(
        &self,
        timeout: Duration,
    ) -> Option<RwLockUpgradableReadGuard<'_, T>> {
        if self.raw.try_lock_upgradable_for(timeout) {
            // SAFETY: The lock is held, as required.
            Some(unsafe { self.upgradable_guard() })
        } else {
            None
        }
    }

    /// Attempts to acquire this `RwLock` with upgradable read access until a timeout
    /// is reached.
    ///
    /// If the access could not be granted before the timeout expires, then
    /// `None` is returned. Otherwise, an RAII guard is returned which will
    /// release the shared access when it is dropped.
    #[inline]
    pub fn try_upgradable_read_until(
        &self,
        timeout: Instant,
    ) -> Option<RwLockUpgradableReadGuard<'_, T>> {
        if self.raw.try_lock_upgradable_until(timeout) {
            // SAFETY: The lock is held, as required.
            Some(unsafe { self.upgradable_guard() })
        } else {
            None
        }
    }
}

impl<T: ?Sized + Default> Default for RwLock<T> {
    #[inline]
    fn default() -> RwLock<T> {
        RwLock::new(Default::default())
    }
}

impl<T> From<T> for RwLock<T> {
    #[inline]
    fn from(t: T) -> RwLock<T> {
        RwLock::new(t)
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for RwLock<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.try_read() {
            Some(guard) => f.debug_struct("RwLock").field("data", &&*guard).finish(),
            None => {
                struct LockedPlaceholder;
                impl fmt::Debug for LockedPlaceholder {
                    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                        f.write_str("<locked>")
                    }
                }

                f.debug_struct("RwLock")
                    .field("data", &LockedPlaceholder)
                    .finish()
            }
        }
    }
}

/// RAII structure used to release the shared read access of a lock when
/// dropped.
#[must_use = "if unused the RwLock will immediately unlock"]
pub struct RwLockReadGuard<'a, T: ?Sized> {
    rwlock: &'a RwLock<T>,
    marker: PhantomData<(&'a T, *mut ())>,
}

unsafe impl<'a, T: ?Sized + Sync + 'a> Sync for RwLockReadGuard<'a, T> {}

impl<'a, T: ?Sized + 'a> RwLockReadGuard<'a, T> {
    /// Returns a reference to the original reader-writer lock object.
    pub fn rwlock(s: &Self) -> &'a RwLock<T> {
        s.rwlock
    }

    /// Make a new `MappedRwLockReadGuard` for a component of the locked data.
    ///
    /// This operation cannot fail as the `RwLockReadGuard` passed
    /// in already locked the data.
    ///
    /// This is an associated function that needs to be
    /// used as `RwLockReadGuard::map(...)`. A method would interfere with methods of
    /// the same name on the contents of the locked data.
    #[inline]
    pub fn map<U: ?Sized, F>(s: Self, f: F) -> MappedRwLockReadGuard<'a, U>
    where
        F: FnOnce(&T) -> &U,
    {
        let raw = &s.rwlock.raw;
        let data = f(unsafe { &*s.rwlock.data.get() });
        mem::forget(s);
        MappedRwLockReadGuard {
            raw,
            data,
            marker: PhantomData,
        }
    }

    /// Attempts to make  a new `MappedRwLockReadGuard` for a component of the
    /// locked data. The original guard is return if the closure returns `None`.
    ///
    /// This operation cannot fail as the `RwLockReadGuard` passed
    /// in already locked the data.
    ///
    /// This is an associated function that needs to be
    /// used as `RwLockReadGuard::map(...)`. A method would interfere with methods of
    /// the same name on the contents of the locked data.
    #[inline]
    pub fn try_map<U: ?Sized, F>(s: Self, f: F) -> Result<MappedRwLockReadGuard<'a, U>, Self>
    where
        F: FnOnce(&T) -> Option<&U>,
    {
        let raw = &s.rwlock.raw;
        let data = match f(unsafe { &*s.rwlock.data.get() }) {
            Some(data) => data,
            None => return Err(s),
        };
        mem::forget(s);
        Ok(MappedRwLockReadGuard {
            raw,
            data,
            marker: PhantomData,
        })
    }

    /// Temporarily unlocks the `RwLock` to execute the given function.
    ///
    /// The `RwLock` is unlocked a fair unlock protocol.
    ///
    /// This is safe because `&mut` guarantees that there exist no other
    /// references to the data protected by the `RwLock`.
    #[inline]
    pub fn unlocked<F, U>(s: &mut Self, f: F) -> U
    where
        F: FnOnce() -> U,
    {
        s.rwlock.raw.unlock_shared();
        defer!(s.rwlock.raw.lock_shared());
        f()
    }
}

impl<'a, T: ?Sized + 'a> RwLockReadGuard<'a, T> {
    /// Unlocks the `RwLock` using a fair unlock protocol.
    ///
    /// By default, `RwLock` is unfair and allow the current thread to re-lock
    /// the `RwLock` before another has the chance to acquire the lock, even if
    /// that thread has been blocked on the `RwLock` for a long time. This is
    /// the default because it allows much higher throughput as it avoids
    /// forcing a context switch on every `RwLock` unlock. This can result in one
    /// thread acquiring a `RwLock` many more times than other threads.
    ///
    /// However in some cases it can be beneficial to ensure fairness by forcing
    /// the lock to pass on to a waiting thread if there is one. This is done by
    /// using this method instead of dropping the `RwLockReadGuard` normally.
    #[inline]
    pub fn unlock_fair(s: Self) {
        s.rwlock.raw.unlock_shared_fair();
        mem::forget(s);
    }

    /// Temporarily unlocks the `RwLock` to execute the given function.
    ///
    /// The `RwLock` is unlocked a fair unlock protocol.
    ///
    /// This is safe because `&mut` guarantees that there exist no other
    /// references to the data protected by the `RwLock`.
    #[inline]
    pub fn unlocked_fair<F, U>(s: &mut Self, f: F) -> U
    where
        F: FnOnce() -> U,
    {
        s.rwlock.raw.unlock_shared_fair();
        defer!(s.rwlock.raw.lock_shared());
        f()
    }

    /// Temporarily yields the `RwLock` to a waiting thread if there is one.
    ///
    /// This method is functionally equivalent to calling `unlock_fair` followed
    /// by `read`, however it can be much more efficient in the case where there
    /// are no waiting threads.
    #[inline]
    pub fn bump(s: &mut Self) {
        s.rwlock.raw.bump_shared();
    }
}

impl<'a, T: ?Sized + 'a> Deref for RwLockReadGuard<'a, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        unsafe { &*self.rwlock.data.get() }
    }
}

impl<'a, T: ?Sized + 'a> Drop for RwLockReadGuard<'a, T> {
    #[inline]
    fn drop(&mut self) {
        self.rwlock.raw.unlock_shared();
    }
}

impl<'a, T: fmt::Debug + ?Sized + 'a> fmt::Debug for RwLockReadGuard<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<'a, T: fmt::Display + ?Sized + 'a> fmt::Display
    for RwLockReadGuard<'a, T>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

#[cfg(feature = "owning_ref_support")]
unsafe impl<'a, T: ?Sized + 'a> StableAddress for RwLockReadGuard<'a, T> {}

/// RAII structure used to release the exclusive write access of a lock when
/// dropped.
#[must_use = "if unused the RwLock will immediately unlock"]
pub struct RwLockWriteGuard<'a, T: ?Sized> {
    rwlock: &'a RwLock<T>,
    marker: PhantomData<(&'a mut T, *mut ())>,
}

unsafe impl<'a, T: ?Sized + Sync + 'a> Sync for RwLockWriteGuard<'a, T> {}

impl<'a, T: ?Sized + 'a> RwLockWriteGuard<'a, T> {
    /// Returns a reference to the original reader-writer lock object.
    pub fn rwlock(s: &Self) -> &'a RwLock<T> {
        s.rwlock
    }

    /// Make a new `MappedRwLockWriteGuard` for a component of the locked data.
    ///
    /// This operation cannot fail as the `RwLockWriteGuard` passed
    /// in already locked the data.
    ///
    /// This is an associated function that needs to be
    /// used as `RwLockWriteGuard::map(...)`. A method would interfere with methods of
    /// the same name on the contents of the locked data.
    #[inline]
    pub fn map<U: ?Sized, F>(s: Self, f: F) -> MappedRwLockWriteGuard<'a, U>
    where
        F: FnOnce(&mut T) -> &mut U,
    {
        let raw = &s.rwlock.raw;
        let data = f(unsafe { &mut *s.rwlock.data.get() });
        mem::forget(s);
        MappedRwLockWriteGuard {
            raw,
            data,
            marker: PhantomData,
        }
    }

    /// Attempts to make  a new `MappedRwLockWriteGuard` for a component of the
    /// locked data. The original guard is return if the closure returns `None`.
    ///
    /// This operation cannot fail as the `RwLockWriteGuard` passed
    /// in already locked the data.
    ///
    /// This is an associated function that needs to be
    /// used as `RwLockWriteGuard::map(...)`. A method would interfere with methods of
    /// the same name on the contents of the locked data.
    #[inline]
    pub fn try_map<U: ?Sized, F>(s: Self, f: F) -> Result<MappedRwLockWriteGuard<'a, U>, Self>
    where
        F: FnOnce(&mut T) -> Option<&mut U>,
    {
        let raw = &s.rwlock.raw;
        let data = match f(unsafe { &mut *s.rwlock.data.get() }) {
            Some(data) => data,
            None => return Err(s),
        };
        mem::forget(s);
        Ok(MappedRwLockWriteGuard {
            raw,
            data,
            marker: PhantomData,
        })
    }

    /// Temporarily unlocks the `RwLock` to execute the given function.
    ///
    /// This is safe because `&mut` guarantees that there exist no other
    /// references to the data protected by the `RwLock`.
    #[inline]
    pub fn unlocked<F, U>(s: &mut Self, f: F) -> U
    where
        F: FnOnce() -> U,
    {
        s.rwlock.raw.unlock_exclusive();
        defer!(s.rwlock.raw.lock_exclusive());
        f()
    }
}

impl<'a, T: ?Sized + 'a> RwLockWriteGuard<'a, T> {
    /// Atomically downgrades a write lock into a read lock without allowing any
    /// writers to take exclusive access of the lock in the meantime.
    ///
    /// Note that if there are any writers currently waiting to take the lock
    /// then other readers may not be able to acquire the lock even if it was
    /// downgraded.
    pub fn downgrade(s: Self) -> RwLockReadGuard<'a, T> {
        s.rwlock.raw.downgrade();
        let rwlock = s.rwlock;
        mem::forget(s);
        RwLockReadGuard {
            rwlock,
            marker: PhantomData,
        }
    }
}

impl<'a, T: ?Sized + 'a> RwLockWriteGuard<'a, T> {
    /// Atomically downgrades a write lock into an upgradable read lock without allowing any
    /// writers to take exclusive access of the lock in the meantime.
    ///
    /// Note that if there are any writers currently waiting to take the lock
    /// then other readers may not be able to acquire the lock even if it was
    /// downgraded.
    pub fn downgrade_to_upgradable(s: Self) -> RwLockUpgradableReadGuard<'a, T> {
        s.rwlock.raw.downgrade_to_upgradable();
        let rwlock = s.rwlock;
        mem::forget(s);
        RwLockUpgradableReadGuard {
            rwlock,
            marker: PhantomData,
        }
    }
}

impl<'a, T: ?Sized + 'a> RwLockWriteGuard<'a, T> {
    /// Unlocks the `RwLock` using a fair unlock protocol.
    ///
    /// By default, `RwLock` is unfair and allow the current thread to re-lock
    /// the `RwLock` before another has the chance to acquire the lock, even if
    /// that thread has been blocked on the `RwLock` for a long time. This is
    /// the default because it allows much higher throughput as it avoids
    /// forcing a context switch on every `RwLock` unlock. This can result in one
    /// thread acquiring a `RwLock` many more times than other threads.
    ///
    /// However in some cases it can be beneficial to ensure fairness by forcing
    /// the lock to pass on to a waiting thread if there is one. This is done by
    /// using this method instead of dropping the `RwLockWriteGuard` normally.
    #[inline]
    pub fn unlock_fair(s: Self) {
        s.rwlock.raw.unlock_exclusive_fair();
        mem::forget(s);
    }

    /// Temporarily unlocks the `RwLock` to execute the given function.
    ///
    /// The `RwLock` is unlocked a fair unlock protocol.
    ///
    /// This is safe because `&mut` guarantees that there exist no other
    /// references to the data protected by the `RwLock`.
    #[inline]
    pub fn unlocked_fair<F, U>(s: &mut Self, f: F) -> U
    where
        F: FnOnce() -> U,
    {
        s.rwlock.raw.unlock_exclusive_fair();
        defer!(s.rwlock.raw.lock_exclusive());
        f()
    }

    /// Temporarily yields the `RwLock` to a waiting thread if there is one.
    ///
    /// This method is functionally equivalent to calling `unlock_fair` followed
    /// by `write`, however it can be much more efficient in the case where there
    /// are no waiting threads.
    #[inline]
    pub fn bump(s: &mut Self) {
        s.rwlock.raw.bump_exclusive();
    }
}

impl<'a, T: ?Sized + 'a> Deref for RwLockWriteGuard<'a, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        unsafe { &*self.rwlock.data.get() }
    }
}

impl<'a, T: ?Sized + 'a> DerefMut for RwLockWriteGuard<'a, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.rwlock.data.get() }
    }
}

impl<'a, T: ?Sized + 'a> Drop for RwLockWriteGuard<'a, T> {
    #[inline]
    fn drop(&mut self) {
        self.rwlock.raw.unlock_exclusive();
    }
}

impl<'a, T: fmt::Debug + ?Sized + 'a> fmt::Debug for RwLockWriteGuard<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<'a, T: fmt::Display + ?Sized + 'a> fmt::Display
    for RwLockWriteGuard<'a, T>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

#[cfg(feature = "owning_ref_support")]
unsafe impl<'a, T: ?Sized + 'a> StableAddress for RwLockWriteGuard<'a, T> {}

/// RAII structure used to release the upgradable read access of a lock when
/// dropped.
#[must_use = "if unused the RwLock will immediately unlock"]
pub struct RwLockUpgradableReadGuard<'a, T: ?Sized> {
    rwlock: &'a RwLock<T>,
    marker: PhantomData<(&'a T, *mut ())>,
}

unsafe impl<'a, T: ?Sized + Sync + 'a> Sync
    for RwLockUpgradableReadGuard<'a, T>
{
}

impl<'a, T: ?Sized + 'a> RwLockUpgradableReadGuard<'a, T> {
    /// Returns a reference to the original reader-writer lock object.
    pub fn rwlock(s: &Self) -> &'a RwLock<T> {
        s.rwlock
    }

    /// Temporarily unlocks the `RwLock` to execute the given function.
    ///
    /// This is safe because `&mut` guarantees that there exist no other
    /// references to the data protected by the `RwLock`.
    #[inline]
    pub fn unlocked<F, U>(s: &mut Self, f: F) -> U
    where
        F: FnOnce() -> U,
    {
        s.rwlock.raw.unlock_upgradable();
        defer!(s.rwlock.raw.lock_upgradable());
        f()
    }

    /// Atomically upgrades an upgradable read lock lock into a exclusive write lock,
    /// blocking the current thread until it can be acquired.
    pub fn upgrade(s: Self) -> RwLockWriteGuard<'a, T> {
        s.rwlock.raw.upgrade();
        let rwlock = s.rwlock;
        mem::forget(s);
        RwLockWriteGuard {
            rwlock,
            marker: PhantomData,
        }
    }

    /// Tries to atomically upgrade an upgradable read lock into a exclusive write lock.
    ///
    /// If the access could not be granted at this time, then the current guard is returned.
    pub fn try_upgrade(s: Self) -> Result<RwLockWriteGuard<'a, T>, Self> {
        if s.rwlock.raw.try_upgrade() {
            let rwlock = s.rwlock;
            mem::forget(s);
            Ok(RwLockWriteGuard {
                rwlock,
                marker: PhantomData,
            })
        } else {
            Err(s)
        }
    }
}

impl<'a, T: ?Sized + 'a> RwLockUpgradableReadGuard<'a, T> {
    /// Unlocks the `RwLock` using a fair unlock protocol.
    ///
    /// By default, `RwLock` is unfair and allow the current thread to re-lock
    /// the `RwLock` before another has the chance to acquire the lock, even if
    /// that thread has been blocked on the `RwLock` for a long time. This is
    /// the default because it allows much higher throughput as it avoids
    /// forcing a context switch on every `RwLock` unlock. This can result in one
    /// thread acquiring a `RwLock` many more times than other threads.
    ///
    /// However in some cases it can be beneficial to ensure fairness by forcing
    /// the lock to pass on to a waiting thread if there is one. This is done by
    /// using this method instead of dropping the `RwLockUpgradableReadGuard` normally.
    #[inline]
    pub fn unlock_fair(s: Self) {
        s.rwlock.raw.unlock_upgradable_fair();
        mem::forget(s);
    }

    /// Temporarily unlocks the `RwLock` to execute the given function.
    ///
    /// The `RwLock` is unlocked a fair unlock protocol.
    ///
    /// This is safe because `&mut` guarantees that there exist no other
    /// references to the data protected by the `RwLock`.
    #[inline]
    pub fn unlocked_fair<F, U>(s: &mut Self, f: F) -> U
    where
        F: FnOnce() -> U,
    {
        s.rwlock.raw.unlock_upgradable_fair();
        defer!(s.rwlock.raw.lock_upgradable());
        f()
    }

    /// Temporarily yields the `RwLock` to a waiting thread if there is one.
    ///
    /// This method is functionally equivalent to calling `unlock_fair` followed
    /// by `upgradable_read`, however it can be much more efficient in the case where there
    /// are no waiting threads.
    #[inline]
    pub fn bump(s: &mut Self) {
        s.rwlock.raw.bump_upgradable();
    }
}

impl<'a, T: ?Sized + 'a> RwLockUpgradableReadGuard<'a, T> {
    /// Atomically downgrades an upgradable read lock lock into a shared read lock
    /// without allowing any writers to take exclusive access of the lock in the
    /// meantime.
    ///
    /// Note that if there are any writers currently waiting to take the lock
    /// then other readers may not be able to acquire the lock even if it was
    /// downgraded.
    pub fn downgrade(s: Self) -> RwLockReadGuard<'a, T> {
        s.rwlock.raw.downgrade_upgradable();
        let rwlock = s.rwlock;
        mem::forget(s);
        RwLockReadGuard {
            rwlock,
            marker: PhantomData,
        }
    }
}

impl<'a, T: ?Sized + 'a> RwLockUpgradableReadGuard<'a, T> {
    /// Tries to atomically upgrade an upgradable read lock into a exclusive
    /// write lock, until a timeout is reached.
    ///
    /// If the access could not be granted before the timeout expires, then
    /// the current guard is returned.
    pub fn try_upgrade_for(
        s: Self,
        timeout: Duration,
    ) -> Result<RwLockWriteGuard<'a, T>, Self> {
        if s.rwlock.raw.try_upgrade_for(timeout) {
            let rwlock = s.rwlock;
            mem::forget(s);
            Ok(RwLockWriteGuard {
                rwlock,
                marker: PhantomData,
            })
        } else {
            Err(s)
        }
    }

    /// Tries to atomically upgrade an upgradable read lock into a exclusive
    /// write lock, until a timeout is reached.
    ///
    /// If the access could not be granted before the timeout expires, then
    /// the current guard is returned.
    #[inline]
    pub fn try_upgrade_until(
        s: Self,
        timeout: Instant,
    ) -> Result<RwLockWriteGuard<'a, T>, Self> {
        if s.rwlock.raw.try_upgrade_until(timeout) {
            let rwlock = s.rwlock;
            mem::forget(s);
            Ok(RwLockWriteGuard {
                rwlock,
                marker: PhantomData,
            })
        } else {
            Err(s)
        }
    }
}

impl<'a, T: ?Sized + 'a> Deref for RwLockUpgradableReadGuard<'a, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        unsafe { &*self.rwlock.data.get() }
    }
}

impl<'a, T: ?Sized + 'a> Drop for RwLockUpgradableReadGuard<'a, T> {
    #[inline]
    fn drop(&mut self) {
        self.rwlock.raw.unlock_upgradable();
    }
}

impl<'a, T: fmt::Debug + ?Sized + 'a> fmt::Debug
    for RwLockUpgradableReadGuard<'a, T>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<'a, T: fmt::Display + ?Sized + 'a> fmt::Display
    for RwLockUpgradableReadGuard<'a, T>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

#[cfg(feature = "owning_ref_support")]
unsafe impl<'a, T: ?Sized + 'a> StableAddress
    for RwLockUpgradableReadGuard<'a, T>
{
}

/// An RAII read lock guard returned by `RwLockReadGuard::map`, which can point to a
/// subfield of the protected data.
///
/// The main difference between `MappedRwLockReadGuard` and `RwLockReadGuard` is that the
/// former doesn't support temporarily unlocking and re-locking, since that
/// could introduce soundness issues if the locked object is modified by another
/// thread.
#[must_use = "if unused the RwLock will immediately unlock"]
pub struct MappedRwLockReadGuard<'a, T: ?Sized> {
    raw: &'a RawRwLock,
    data: *const T,
    marker: PhantomData<&'a T>,
}

unsafe impl<'a, T: ?Sized + Sync + 'a> Sync for MappedRwLockReadGuard<'a, T> {}

impl<'a, T: ?Sized + 'a> MappedRwLockReadGuard<'a, T> {
    /// Make a new `MappedRwLockReadGuard` for a component of the locked data.
    ///
    /// This operation cannot fail as the `MappedRwLockReadGuard` passed
    /// in already locked the data.
    ///
    /// This is an associated function that needs to be
    /// used as `MappedRwLockReadGuard::map(...)`. A method would interfere with methods of
    /// the same name on the contents of the locked data.
    #[inline]
    pub fn map<U: ?Sized, F>(s: Self, f: F) -> MappedRwLockReadGuard<'a, U>
    where
        F: FnOnce(&T) -> &U,
    {
        let raw = s.raw;
        let data = f(unsafe { &*s.data });
        mem::forget(s);
        MappedRwLockReadGuard {
            raw,
            data,
            marker: PhantomData,
        }
    }

    /// Attempts to make  a new `MappedRwLockReadGuard` for a component of the
    /// locked data. The original guard is return if the closure returns `None`.
    ///
    /// This operation cannot fail as the `MappedRwLockReadGuard` passed
    /// in already locked the data.
    ///
    /// This is an associated function that needs to be
    /// used as `MappedRwLockReadGuard::map(...)`. A method would interfere with methods of
    /// the same name on the contents of the locked data.
    #[inline]
    pub fn try_map<U: ?Sized, F>(s: Self, f: F) -> Result<MappedRwLockReadGuard<'a, U>, Self>
    where
        F: FnOnce(&T) -> Option<&U>,
    {
        let raw = s.raw;
        let data = match f(unsafe { &*s.data }) {
            Some(data) => data,
            None => return Err(s),
        };
        mem::forget(s);
        Ok(MappedRwLockReadGuard {
            raw,
            data,
            marker: PhantomData,
        })
    }
}

impl<'a, T: ?Sized + 'a> MappedRwLockReadGuard<'a, T> {
    /// Unlocks the `RwLock` using a fair unlock protocol.
    ///
    /// By default, `RwLock` is unfair and allow the current thread to re-lock
    /// the `RwLock` before another has the chance to acquire the lock, even if
    /// that thread has been blocked on the `RwLock` for a long time. This is
    /// the default because it allows much higher throughput as it avoids
    /// forcing a context switch on every `RwLock` unlock. This can result in one
    /// thread acquiring a `RwLock` many more times than other threads.
    ///
    /// However in some cases it can be beneficial to ensure fairness by forcing
    /// the lock to pass on to a waiting thread if there is one. This is done by
    /// using this method instead of dropping the `MappedRwLockReadGuard` normally.
    #[inline]
    pub fn unlock_fair(s: Self) {
        s.raw.unlock_shared_fair();
        mem::forget(s);
    }
}

impl<'a, T: ?Sized + 'a> Deref for MappedRwLockReadGuard<'a, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        unsafe { &*self.data }
    }
}

impl<'a, T: ?Sized + 'a> Drop for MappedRwLockReadGuard<'a, T> {
    #[inline]
    fn drop(&mut self) {
        self.raw.unlock_shared();
    }
}

impl<'a, T: fmt::Debug + ?Sized + 'a> fmt::Debug
    for MappedRwLockReadGuard<'a, T>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<'a, T: fmt::Display + ?Sized + 'a> fmt::Display
    for MappedRwLockReadGuard<'a, T>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

#[cfg(feature = "owning_ref_support")]
unsafe impl<'a, T: ?Sized + 'a> StableAddress
    for MappedRwLockReadGuard<'a, T>
{
}

/// An RAII write lock guard returned by `RwLockWriteGuard::map`, which can point to a
/// subfield of the protected data.
///
/// The main difference between `MappedRwLockWriteGuard` and `RwLockWriteGuard` is that the
/// former doesn't support temporarily unlocking and re-locking, since that
/// could introduce soundness issues if the locked object is modified by another
/// thread.
#[must_use = "if unused the RwLock will immediately unlock"]
pub struct MappedRwLockWriteGuard<'a, T: ?Sized> {
    raw: &'a RawRwLock,
    data: *mut T,
    marker: PhantomData<&'a mut T>,
}

unsafe impl<'a, T: ?Sized + Sync + 'a> Sync
    for MappedRwLockWriteGuard<'a, T>
{
}

impl<'a, T: ?Sized + 'a> MappedRwLockWriteGuard<'a, T> {
    /// Make a new `MappedRwLockWriteGuard` for a component of the locked data.
    ///
    /// This operation cannot fail as the `MappedRwLockWriteGuard` passed
    /// in already locked the data.
    ///
    /// This is an associated function that needs to be
    /// used as `MappedRwLockWriteGuard::map(...)`. A method would interfere with methods of
    /// the same name on the contents of the locked data.
    #[inline]
    pub fn map<U: ?Sized, F>(s: Self, f: F) -> MappedRwLockWriteGuard<'a, U>
    where
        F: FnOnce(&mut T) -> &mut U,
    {
        let raw = s.raw;
        let data = f(unsafe { &mut *s.data });
        mem::forget(s);
        MappedRwLockWriteGuard {
            raw,
            data,
            marker: PhantomData,
        }
    }

    /// Attempts to make  a new `MappedRwLockWriteGuard` for a component of the
    /// locked data. The original guard is return if the closure returns `None`.
    ///
    /// This operation cannot fail as the `MappedRwLockWriteGuard` passed
    /// in already locked the data.
    ///
    /// This is an associated function that needs to be
    /// used as `MappedRwLockWriteGuard::map(...)`. A method would interfere with methods of
    /// the same name on the contents of the locked data.
    #[inline]
    pub fn try_map<U: ?Sized, F>(s: Self, f: F) -> Result<MappedRwLockWriteGuard<'a, U>, Self>
    where
        F: FnOnce(&mut T) -> Option<&mut U>,
    {
        let raw = s.raw;
        let data = match f(unsafe { &mut *s.data }) {
            Some(data) => data,
            None => return Err(s),
        };
        mem::forget(s);
        Ok(MappedRwLockWriteGuard {
            raw,
            data,
            marker: PhantomData,
        })
    }
}

impl<'a, T: ?Sized + 'a> MappedRwLockWriteGuard<'a, T> {
    /// Atomically downgrades a write lock into a read lock without allowing any
    /// writers to take exclusive access of the lock in the meantime.
    ///
    /// Note that if there are any writers currently waiting to take the lock
    /// then other readers may not be able to acquire the lock even if it was
    /// downgraded.
    pub fn downgrade(s: Self) -> MappedRwLockReadGuard<'a, T> {
        s.raw.downgrade();
        let raw = s.raw;
        let data = s.data;
        mem::forget(s);
        MappedRwLockReadGuard {
            raw,
            data,
            marker: PhantomData,
        }
    }
}

impl<'a, T: ?Sized + 'a> MappedRwLockWriteGuard<'a, T> {
    /// Unlocks the `RwLock` using a fair unlock protocol.
    ///
    /// By default, `RwLock` is unfair and allow the current thread to re-lock
    /// the `RwLock` before another has the chance to acquire the lock, even if
    /// that thread has been blocked on the `RwLock` for a long time. This is
    /// the default because it allows much higher throughput as it avoids
    /// forcing a context switch on every `RwLock` unlock. This can result in one
    /// thread acquiring a `RwLock` many more times than other threads.
    ///
    /// However in some cases it can be beneficial to ensure fairness by forcing
    /// the lock to pass on to a waiting thread if there is one. This is done by
    /// using this method instead of dropping the `MappedRwLockWriteGuard` normally.
    #[inline]
    pub fn unlock_fair(s: Self) {
        s.raw.unlock_exclusive_fair();
        mem::forget(s);
    }
}

impl<'a, T: ?Sized + 'a> Deref for MappedRwLockWriteGuard<'a, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        unsafe { &*self.data }
    }
}

impl<'a, T: ?Sized + 'a> DerefMut for MappedRwLockWriteGuard<'a, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.data }
    }
}

impl<'a, T: ?Sized + 'a> Drop for MappedRwLockWriteGuard<'a, T> {
    #[inline]
    fn drop(&mut self) {
        self.raw.unlock_exclusive();
    }
}

impl<'a, T: fmt::Debug + ?Sized + 'a> fmt::Debug
    for MappedRwLockWriteGuard<'a, T>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<'a, T: fmt::Display + ?Sized + 'a> fmt::Display
    for MappedRwLockWriteGuard<'a, T>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

#[cfg(feature = "owning_ref_support")]
unsafe impl<'a, T: ?Sized + 'a> StableAddress
    for MappedRwLockWriteGuard<'a, T>
{
}


#[cfg(test)]
mod tests {
    use crate::{RwLock, RwLockUpgradableReadGuard, RwLockWriteGuard};
    use rand::Rng;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::mpsc::channel;
    use std::sync::Arc;
    use std::thread;
    use std::time::Duration;

    #[cfg(feature = "serde_support")]
    use bincode::{deserialize, serialize};

    #[derive(Eq, PartialEq, Debug)]
    struct NonCopy(i32);

    #[test]
    fn smoke() {
        let l = RwLock::new(());
        drop(l.read());
        drop(l.write());
        drop(l.upgradable_read());
        drop((l.read(), l.read()));
        drop((l.read(), l.upgradable_read()));
        drop(l.write());
    }

    #[test]
    fn frob() {
        const N: u32 = 10;
        const M: u32 = 1000;

        let r = Arc::new(RwLock::new(()));

        let (tx, rx) = channel::<()>();
        for _ in 0..N {
            let tx = tx.clone();
            let r = r.clone();
            thread::spawn(move || {
                let mut rng = rand::thread_rng();
                for _ in 0..M {
                    if rng.gen_bool(1.0 / N as f64) {
                        drop(r.write());
                    } else {
                        drop(r.read());
                    }
                }
                drop(tx);
            });
        }
        drop(tx);
        let _ = rx.recv();
    }

    #[test]
    fn test_rw_arc_no_poison_wr() {
        let arc = Arc::new(RwLock::new(1));
        let arc2 = arc.clone();
        let _: Result<(), _> = thread::spawn(move || {
            let _lock = arc2.write();
            panic!();
        })
        .join();
        let lock = arc.read();
        assert_eq!(*lock, 1);
    }

    #[test]
    fn test_rw_arc_no_poison_ww() {
        let arc = Arc::new(RwLock::new(1));
        let arc2 = arc.clone();
        let _: Result<(), _> = thread::spawn(move || {
            let _lock = arc2.write();
            panic!();
        })
        .join();
        let lock = arc.write();
        assert_eq!(*lock, 1);
    }

    #[test]
    fn test_rw_arc_no_poison_rr() {
        let arc = Arc::new(RwLock::new(1));
        let arc2 = arc.clone();
        let _: Result<(), _> = thread::spawn(move || {
            let _lock = arc2.read();
            panic!();
        })
        .join();
        let lock = arc.read();
        assert_eq!(*lock, 1);
    }

    #[test]
    fn test_rw_arc_no_poison_rw() {
        let arc = Arc::new(RwLock::new(1));
        let arc2 = arc.clone();
        let _: Result<(), _> = thread::spawn(move || {
            let _lock = arc2.read();
            panic!()
        })
        .join();
        let lock = arc.write();
        assert_eq!(*lock, 1);
    }

    #[test]
    fn test_ruw_arc() {
        let arc = Arc::new(RwLock::new(0));
        let arc2 = arc.clone();
        let (tx, rx) = channel();

        thread::spawn(move || {
            for _ in 0..10 {
                let mut lock = arc2.write();
                let tmp = *lock;
                *lock = -1;
                thread::yield_now();
                *lock = tmp + 1;
            }
            tx.send(()).unwrap();
        });

        let mut children = Vec::new();

        // Upgradable readers try to catch the writer in the act and also
        // try to touch the value
        for _ in 0..5 {
            let arc3 = arc.clone();
            children.push(thread::spawn(move || {
                let lock = arc3.upgradable_read();
                let tmp = *lock;
                assert!(tmp >= 0);
                thread::yield_now();
                let mut lock = RwLockUpgradableReadGuard::upgrade(lock);
                assert_eq!(tmp, *lock);
                *lock = -1;
                thread::yield_now();
                *lock = tmp + 1;
            }));
        }

        // Readers try to catch the writers in the act
        for _ in 0..5 {
            let arc4 = arc.clone();
            children.push(thread::spawn(move || {
                let lock = arc4.read();
                assert!(*lock >= 0);
            }));
        }

        // Wait for children to pass their asserts
        for r in children {
            assert!(r.join().is_ok());
        }

        // Wait for writer to finish
        rx.recv().unwrap();
        let lock = arc.read();
        assert_eq!(*lock, 15);
    }

    #[test]
    fn test_rw_arc() {
        let arc = Arc::new(RwLock::new(0));
        let arc2 = arc.clone();
        let (tx, rx) = channel();

        thread::spawn(move || {
            let mut lock = arc2.write();
            for _ in 0..10 {
                let tmp = *lock;
                *lock = -1;
                thread::yield_now();
                *lock = tmp + 1;
            }
            tx.send(()).unwrap();
        });

        // Readers try to catch the writer in the act
        let mut children = Vec::new();
        for _ in 0..5 {
            let arc3 = arc.clone();
            children.push(thread::spawn(move || {
                let lock = arc3.read();
                assert!(*lock >= 0);
            }));
        }

        // Wait for children to pass their asserts
        for r in children {
            assert!(r.join().is_ok());
        }

        // Wait for writer to finish
        rx.recv().unwrap();
        let lock = arc.read();
        assert_eq!(*lock, 10);
    }

    #[test]
    fn test_rw_arc_access_in_unwind() {
        let arc = Arc::new(RwLock::new(1));
        let arc2 = arc.clone();
        let _ = thread::spawn(move || {
            struct Unwinder {
                i: Arc<RwLock<isize>>,
            }
            impl Drop for Unwinder {
                fn drop(&mut self) {
                    let mut lock = self.i.write();
                    *lock += 1;
                }
            }
            let _u = Unwinder { i: arc2 };
            panic!();
        })
        .join();
        let lock = arc.read();
        assert_eq!(*lock, 2);
    }

    #[test]
    fn test_rwlock_unsized() {
        let rw: &RwLock<[i32]> = &RwLock::new([1, 2, 3]);
        {
            let b = &mut *rw.write();
            b[0] = 4;
            b[2] = 5;
        }
        let comp: &[i32] = &[4, 2, 5];
        assert_eq!(&*rw.read(), comp);
    }

    #[test]
    fn test_rwlock_try_read() {
        let lock = RwLock::new(0isize);
        {
            let read_guard = lock.read();

            let read_result = lock.try_read();
            assert!(
                read_result.is_some(),
                "try_read should succeed while read_guard is in scope"
            );

            drop(read_guard);
        }
        {
            let upgrade_guard = lock.upgradable_read();

            let read_result = lock.try_read();
            assert!(
                read_result.is_some(),
                "try_read should succeed while upgrade_guard is in scope"
            );

            drop(upgrade_guard);
        }
        {
            let write_guard = lock.write();

            let read_result = lock.try_read();
            assert!(
                read_result.is_none(),
                "try_read should fail while write_guard is in scope"
            );

            drop(write_guard);
        }
    }

    #[test]
    fn test_rwlock_try_write() {
        let lock = RwLock::new(0isize);
        {
            let read_guard = lock.read();

            let write_result = lock.try_write();
            assert!(
                write_result.is_none(),
                "try_write should fail while read_guard is in scope"
            );

            drop(read_guard);
        }
        {
            let upgrade_guard = lock.upgradable_read();

            let write_result = lock.try_write();
            assert!(
                write_result.is_none(),
                "try_write should fail while upgrade_guard is in scope"
            );

            drop(upgrade_guard);
        }
        {
            let write_guard = lock.write();

            let write_result = lock.try_write();
            assert!(
                write_result.is_none(),
                "try_write should fail while write_guard is in scope"
            );

            drop(write_guard);
        }
    }

    #[test]
    fn test_rwlock_try_upgrade() {
        let lock = RwLock::new(0isize);
        {
            let read_guard = lock.read();

            let upgrade_result = lock.try_upgradable_read();
            assert!(
                upgrade_result.is_some(),
                "try_upgradable_read should succeed while read_guard is in scope"
            );

            drop(read_guard);
        }
        {
            let upgrade_guard = lock.upgradable_read();

            let upgrade_result = lock.try_upgradable_read();
            assert!(
                upgrade_result.is_none(),
                "try_upgradable_read should fail while upgrade_guard is in scope"
            );

            drop(upgrade_guard);
        }
        {
            let write_guard = lock.write();

            let upgrade_result = lock.try_upgradable_read();
            assert!(
                upgrade_result.is_none(),
                "try_upgradable should fail while write_guard is in scope"
            );

            drop(write_guard);
        }
    }

    #[test]
    fn test_into_inner() {
        let m = RwLock::new(NonCopy(10));
        assert_eq!(m.into_inner(), NonCopy(10));
    }

    #[test]
    fn test_into_inner_drop() {
        struct Foo(Arc<AtomicUsize>);
        impl Drop for Foo {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }
        let num_drops = Arc::new(AtomicUsize::new(0));
        let m = RwLock::new(Foo(num_drops.clone()));
        assert_eq!(num_drops.load(Ordering::SeqCst), 0);
        {
            let _inner = m.into_inner();
            assert_eq!(num_drops.load(Ordering::SeqCst), 0);
        }
        assert_eq!(num_drops.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn test_get_mut() {
        let mut m = RwLock::new(NonCopy(10));
        *m.get_mut() = NonCopy(20);
        assert_eq!(m.into_inner(), NonCopy(20));
    }

    #[test]
    fn test_rwlockguard_sync() {
        fn sync<T: Sync>(_: T) {}

        let rwlock = RwLock::new(());
        sync(rwlock.read());
        sync(rwlock.write());
    }

    #[test]
    fn test_rwlock_downgrade() {
        let x = Arc::new(RwLock::new(0));
        let mut handles = Vec::new();
        for _ in 0..8 {
            let x = x.clone();
            handles.push(thread::spawn(move || {
                for _ in 0..100 {
                    let mut writer = x.write();
                    *writer += 1;
                    let cur_val = *writer;
                    let reader = RwLockWriteGuard::downgrade(writer);
                    assert_eq!(cur_val, *reader);
                }
            }));
        }
        for handle in handles {
            handle.join().unwrap()
        }
        assert_eq!(*x.read(), 800);
    }

    #[test]
    fn test_rwlock_recursive() {
        let arc = Arc::new(RwLock::new(1));
        let arc2 = arc.clone();
        let _lock1 = arc.read();
        thread::spawn(move || {
            let _lock = arc2.write();
        });

        if cfg!(not(all(target_env = "sgx", target_vendor = "fortanix"))) {
            thread::sleep(Duration::from_millis(100));
        } else {
            // FIXME: https://github.com/fortanix/rust-sgx/issues/31
            for _ in 0..100 {
                thread::yield_now();
            }
        }

        // A normal read would block here since there is a pending writer
        let _lock2 = arc.read_recursive();
    }

    #[test]
    fn test_rwlock_debug() {
        let x = RwLock::new(vec![0u8, 10]);

        assert_eq!(format!("{:?}", x), "RwLock { data: [0, 10] }");
        let _lock = x.write();
        assert_eq!(format!("{:?}", x), "RwLock { data: <locked> }");
    }

    #[test]
    fn test_clone() {
        let rwlock = RwLock::new(Arc::new(1));
        let a = rwlock.read_recursive();
        let b = a.clone();
        assert_eq!(Arc::strong_count(&b), 2);
    }

    #[cfg(feature = "serde_support")]
    #[test]
    fn test_serde() {
        let contents: Vec<u8> = vec![0, 1, 2];
        let mutex = RwLock::new(contents.clone());

        let serialized = serialize(&mutex).unwrap();
        let deserialized: RwLock<Vec<u8>> = deserialize(&serialized).unwrap();

        assert_eq!(*(mutex.read()), *(deserialized.read()));
        assert_eq!(contents, *(deserialized.read()));
    }
}
