// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.
use parking_lot::{
    lock_api::{
        RawMutex as _,
        RawMutexFair as _,
        RawMutexTimed as _,
    },
    RawMutex,
};
use core::{
    cell::{Cell, UnsafeCell},
    fmt,
    marker::PhantomData,
    mem,
    num::NonZeroUsize,
    ops::Deref,
    sync::atomic::{AtomicUsize, Ordering},
    time::Duration,
};
use std::time::Instant;

#[cfg(feature = "owning_ref_support")]
use owning_ref::StableAddress;

#[cfg(feature = "serde_support")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};


fn nonzero_thread_id() -> NonZeroUsize {
    // The address of a thread-local variable is guaranteed to be unique to the
    // current thread, and is also guaranteed to be non-zero. The variable has to have a
    // non-zero size to guarantee it has a unique address for each thread.
    thread_local!(static KEY: u8 = 0);
    KEY.with(|x| {
        NonZeroUsize::new(x as *const _ as usize)
            .expect("thread-local variable address is null")
    })
}

struct RawReentrantMutex {
    owner: AtomicUsize,
    lock_count: Cell<usize>,
    mutex: RawMutex,
}

impl RawReentrantMutex {
    #[inline]
    fn lock_internal<F: FnOnce() -> bool>(&self, try_lock: F) -> bool {
        let id = nonzero_thread_id().get();
        if self.owner.load(Ordering::Relaxed) == id {
            self.lock_count.set(
                self.lock_count
                    .get()
                    .checked_add(1)
                    .expect("ReentrantMutex lock count overflow"),
            );
        } else {
            if !try_lock() {
                return false;
            }
            self.owner.store(id, Ordering::Relaxed);
            debug_assert_eq!(self.lock_count.get(), 0);
            self.lock_count.set(1);
        }
        true
    }

    #[inline]
    fn lock(&self) {
        self.lock_internal(|| {
            self.mutex.lock();
            true
        });
    }

    #[inline]
    fn try_lock(&self) -> bool {
        self.lock_internal(|| self.mutex.try_lock())
    }

    #[inline]
    fn unlock(&self) {
        let lock_count = self.lock_count.get() - 1;
        self.lock_count.set(lock_count);
        if lock_count == 0 {
            self.owner.store(0, Ordering::Relaxed);
            self.mutex.unlock();
        }
    }
}

impl RawReentrantMutex {
    #[inline]
    fn unlock_fair(&self) {
        let lock_count = self.lock_count.get() - 1;
        self.lock_count.set(lock_count);
        if lock_count == 0 {
            self.owner.store(0, Ordering::Relaxed);
            self.mutex.unlock_fair();
        }
    }

    #[inline]
    fn bump(&self) {
        if self.lock_count.get() == 1 {
            let id = self.owner.load(Ordering::Relaxed);
            self.owner.store(0, Ordering::Relaxed);
            self.mutex.bump();
            self.owner.store(id, Ordering::Relaxed);
        }
    }
}

impl RawReentrantMutex {
    #[inline]
    fn try_lock_until(&self, timeout: Instant) -> bool {
        self.lock_internal(|| self.mutex.try_lock_until(timeout))
    }

    #[inline]
    fn try_lock_for(&self, timeout: Duration) -> bool {
        self.lock_internal(|| self.mutex.try_lock_for(timeout))
    }
}

/// A mutex which can be recursively locked by a single thread.
///
/// This type is identical to `Mutex` except for the following points:
///
/// - Locking multiple times from the same thread will work correctly instead of
///   deadlocking.
/// - `ReentrantMutexGuard` does not give mutable references to the locked data.
///   Use a `RefCell` if you need this.
///
/// See [`Mutex`](struct.Mutex.html) for more details about the underlying mutex
/// primitive.
pub struct ReentrantMutex<T: ?Sized> {
    raw: RawReentrantMutex,
    data: UnsafeCell<T>,
}

unsafe impl<T: ?Sized + Send> Send
    for ReentrantMutex<T>
{
}
unsafe impl<T: ?Sized + Send> Sync
    for ReentrantMutex<T>
{
}

impl<T> ReentrantMutex<T> {
    /// Creates a new reentrant mutex in an unlocked state ready for use.
    #[inline]
    pub const fn new(val: T) -> ReentrantMutex<T> {
        ReentrantMutex {
            data: UnsafeCell::new(val),
            raw: RawReentrantMutex {
                owner: AtomicUsize::new(0),
                lock_count: Cell::new(0),
                mutex: RawMutex::INIT,
            },
        }
    }

    /// Consumes this mutex, returning the underlying data.
    #[inline]
    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }
}

impl<T: ?Sized> ReentrantMutex<T> {
    /// # Safety
    ///
    /// The lock must be held when calling this method.
    #[inline]
    unsafe fn guard(&self) -> ReentrantMutexGuard<'_, T> {
        ReentrantMutexGuard {
            remutex: &self,
            marker: PhantomData,
        }
    }

    /// Acquires a reentrant mutex, blocking the current thread until it is able
    /// to do so.
    ///
    /// If the mutex is held by another thread then this function will block the
    /// local thread until it is available to acquire the mutex. If the mutex is
    /// already held by the current thread then this function will increment the
    /// lock reference count and return immediately. Upon returning,
    /// the thread is the only thread with the mutex held. An RAII guard is
    /// returned to allow scoped unlock of the lock. When the guard goes out of
    /// scope, the mutex will be unlocked.
    #[inline]
    pub fn lock(&self) -> ReentrantMutexGuard<'_, T> {
        self.raw.lock();
        // SAFETY: The lock is held, as required.
        unsafe { self.guard() }
    }

    /// Attempts to acquire this lock.
    ///
    /// If the lock could not be acquired at this time, then `None` is returned.
    /// Otherwise, an RAII guard is returned. The lock will be unlocked when the
    /// guard is dropped.
    ///
    /// This function does not block.
    #[inline]
    pub fn try_lock(&self) -> Option<ReentrantMutexGuard<'_, T>> {
        if self.raw.try_lock() {
            // SAFETY: The lock is held, as required.
            Some(unsafe { self.guard() })
        } else {
            None
        }
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the `ReentrantMutex` mutably, no actual locking needs to
    /// take place---the mutable borrow statically guarantees no locks exist.
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        unsafe { &mut *self.data.get() }
    }

    /// Forcibly unlocks the mutex.
    ///
    /// This is useful when combined with `mem::forget` to hold a lock without
    /// the need to maintain a `ReentrantMutexGuard` object alive, for example when
    /// dealing with FFI.
    ///
    /// # Safety
    ///
    /// This method must only be called if the current thread logically owns a
    /// `ReentrantMutexGuard` but that guard has be discarded using `mem::forget`.
    /// Behavior is undefined if a mutex is unlocked when not locked.
    #[inline]
    pub unsafe fn force_unlock(&self) {
        self.raw.unlock();
    }

    /// Returns the underlying raw mutex object.
    ///
    /// Note that you will most likely need to import the `RawMutex` trait from
    /// `lock_api` to be able to call functions on the raw mutex.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it allows unlocking a mutex while
    /// still holding a reference to a `ReentrantMutexGuard`.
    #[inline]
    pub unsafe fn raw(&self) -> &RawMutex {
        &self.raw.mutex
    }
}

impl<T: ?Sized> ReentrantMutex<T> {
    /// Forcibly unlocks the mutex using a fair unlock protocol.
    ///
    /// This is useful when combined with `mem::forget` to hold a lock without
    /// the need to maintain a `ReentrantMutexGuard` object alive, for example when
    /// dealing with FFI.
    ///
    /// # Safety
    ///
    /// This method must only be called if the current thread logically owns a
    /// `ReentrantMutexGuard` but that guard has be discarded using `mem::forget`.
    /// Behavior is undefined if a mutex is unlocked when not locked.
    #[inline]
    pub unsafe fn force_unlock_fair(&self) {
        self.raw.unlock_fair();
    }
}

impl<T: ?Sized> ReentrantMutex<T> {
    /// Attempts to acquire this lock until a timeout is reached.
    ///
    /// If the lock could not be acquired before the timeout expired, then
    /// `None` is returned. Otherwise, an RAII guard is returned. The lock will
    /// be unlocked when the guard is dropped.
    #[inline]
    pub fn try_lock_for(&self, timeout: Duration) -> Option<ReentrantMutexGuard<'_, T>> {
        if self.raw.try_lock_for(timeout) {
            // SAFETY: The lock is held, as required.
            Some(unsafe { self.guard() })
        } else {
            None
        }
    }

    /// Attempts to acquire this lock until a timeout is reached.
    ///
    /// If the lock could not be acquired before the timeout expired, then
    /// `None` is returned. Otherwise, an RAII guard is returned. The lock will
    /// be unlocked when the guard is dropped.
    #[inline]
    pub fn try_lock_until(&self, timeout: Instant) -> Option<ReentrantMutexGuard<'_, T>> {
        if self.raw.try_lock_until(timeout) {
            // SAFETY: The lock is held, as required.
            Some(unsafe { self.guard() })
        } else {
            None
        }
    }
}

impl<T: ?Sized + Default> Default for ReentrantMutex<T> {
    #[inline]
    fn default() -> ReentrantMutex<T> {
        ReentrantMutex::new(Default::default())
    }
}

impl<T> From<T> for ReentrantMutex<T> {
    #[inline]
    fn from(t: T) -> ReentrantMutex<T> {
        ReentrantMutex::new(t)
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for ReentrantMutex<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.try_lock() {
            Some(guard) => f
                .debug_struct("ReentrantMutex")
                .field("data", &&*guard)
                .finish(),
            None => {
                struct LockedPlaceholder;
                impl fmt::Debug for LockedPlaceholder {
                    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                        f.write_str("<locked>")
                    }
                }

                f.debug_struct("ReentrantMutex")
                    .field("data", &LockedPlaceholder)
                    .finish()
            }
        }
    }
}

// Copied and modified from serde
#[cfg(feature = "serde_support")]
impl<T> Serialize for ReentrantMutex<T>
where
    T: Serialize + ?Sized,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.lock().serialize(serializer)
    }
}

#[cfg(feature = "serde_support")]
impl<'de, T> Deserialize<'de> for ReentrantMutex<T>
where
    T: Deserialize<'de> + ?Sized,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Deserialize::deserialize(deserializer).map(ReentrantMutex::new)
    }
}

/// An RAII implementation of a "scoped lock" of a reentrant mutex. When this structure
/// is dropped (falls out of scope), the lock will be unlocked.
///
/// The data protected by the mutex can be accessed through this guard via its
/// `Deref` implementation.
#[must_use = "if unused the ReentrantMutex will immediately unlock"]
pub struct ReentrantMutexGuard<'a, T: ?Sized> {
    remutex: &'a ReentrantMutex<T>,
    marker: PhantomData<(&'a T, *mut ())>,
}

unsafe impl<'a, T: ?Sized + Sync + 'a> Sync
    for ReentrantMutexGuard<'a, T>
{
}

impl<'a, T: ?Sized + 'a> ReentrantMutexGuard<'a, T> {
    /// Returns a reference to the original `ReentrantMutex` object.
    pub fn remutex(s: &Self) -> &'a ReentrantMutex<T> {
        s.remutex
    }

    /// Makes a new `MappedReentrantMutexGuard` for a component of the locked data.
    ///
    /// This operation cannot fail as the `ReentrantMutexGuard` passed
    /// in already locked the mutex.
    ///
    /// This is an associated function that needs to be
    /// used as `ReentrantMutexGuard::map(...)`. A method would interfere with methods of
    /// the same name on the contents of the locked data.
    #[inline]
    pub fn map<U: ?Sized, F>(s: Self, f: F) -> MappedReentrantMutexGuard<'a, U>
    where
        F: FnOnce(&T) -> &U,
    {
        let raw = &s.remutex.raw;
        let data = f(unsafe { &*s.remutex.data.get() });
        mem::forget(s);
        MappedReentrantMutexGuard {
            raw,
            data,
            marker: PhantomData,
        }
    }

    /// Attempts to make  a new `MappedReentrantMutexGuard` for a component of the
    /// locked data. The original guard is return if the closure returns `None`.
    ///
    /// This operation cannot fail as the `ReentrantMutexGuard` passed
    /// in already locked the mutex.
    ///
    /// This is an associated function that needs to be
    /// used as `ReentrantMutexGuard::map(...)`. A method would interfere with methods of
    /// the same name on the contents of the locked data.
    #[inline]
    pub fn try_map<U: ?Sized, F>(
        s: Self,
        f: F,
    ) -> Result<MappedReentrantMutexGuard<'a, U>, Self>
    where
        F: FnOnce(&mut T) -> Option<&mut U>,
    {
        let raw = &s.remutex.raw;
        let data = match f(unsafe { &mut *s.remutex.data.get() }) {
            Some(data) => data,
            None => return Err(s),
        };
        mem::forget(s);
        Ok(MappedReentrantMutexGuard {
            raw,
            data,
            marker: PhantomData,
        })
    }

    /// Temporarily unlocks the mutex to execute the given function.
    ///
    /// This is safe because `&mut` guarantees that there exist no other
    /// references to the data protected by the mutex.
    #[inline]
    pub fn unlocked<F, U>(s: &mut Self, f: F) -> U
    where
        F: FnOnce() -> U,
    {
        s.remutex.raw.unlock();
        defer!(s.remutex.raw.lock());
        f()
    }
}

impl<'a, T: ?Sized + 'a>
    ReentrantMutexGuard<'a, T>
{
    /// Unlocks the mutex using a fair unlock protocol.
    ///
    /// By default, mutexes are unfair and allow the current thread to re-lock
    /// the mutex before another has the chance to acquire the lock, even if
    /// that thread has been blocked on the mutex for a long time. This is the
    /// default because it allows much higher throughput as it avoids forcing a
    /// context switch on every mutex unlock. This can result in one thread
    /// acquiring a mutex many more times than other threads.
    ///
    /// However in some cases it can be beneficial to ensure fairness by forcing
    /// the lock to pass on to a waiting thread if there is one. This is done by
    /// using this method instead of dropping the `ReentrantMutexGuard` normally.
    #[inline]
    pub fn unlock_fair(s: Self) {
        s.remutex.raw.unlock_fair();
        mem::forget(s);
    }

    /// Temporarily unlocks the mutex to execute the given function.
    ///
    /// The mutex is unlocked a fair unlock protocol.
    ///
    /// This is safe because `&mut` guarantees that there exist no other
    /// references to the data protected by the mutex.
    #[inline]
    pub fn unlocked_fair<F, U>(s: &mut Self, f: F) -> U
    where
        F: FnOnce() -> U,
    {
        s.remutex.raw.unlock_fair();
        defer!(s.remutex.raw.lock());
        f()
    }

    /// Temporarily yields the mutex to a waiting thread if there is one.
    ///
    /// This method is functionally equivalent to calling `unlock_fair` followed
    /// by `lock`, however it can be much more efficient in the case where there
    /// are no waiting threads.
    #[inline]
    pub fn bump(s: &mut Self) {
        s.remutex.raw.bump();
    }
}

impl<'a, T: ?Sized + 'a> Deref
    for ReentrantMutexGuard<'a, T>
{
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        unsafe { &*self.remutex.data.get() }
    }
}

impl<'a, T: ?Sized + 'a> Drop
    for ReentrantMutexGuard<'a, T>
{
    #[inline]
    fn drop(&mut self) {
        self.remutex.raw.unlock();
    }
}

impl<'a, T: fmt::Debug + ?Sized + 'a> fmt::Debug
    for ReentrantMutexGuard<'a, T>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<'a, T: fmt::Display + ?Sized + 'a> fmt::Display
    for ReentrantMutexGuard<'a, T>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

#[cfg(feature = "owning_ref_support")]
unsafe impl<'a, T: ?Sized + 'a> StableAddress
    for ReentrantMutexGuard<'a, T>
{
}

/// An RAII mutex guard returned by `ReentrantMutexGuard::map`, which can point to a
/// subfield of the protected data.
///
/// The main difference between `MappedReentrantMutexGuard` and `ReentrantMutexGuard` is that the
/// former doesn't support temporarily unlocking and re-locking, since that
/// could introduce soundness issues if the locked object is modified by another
/// thread.
#[must_use = "if unused the ReentrantMutex will immediately unlock"]
pub struct MappedReentrantMutexGuard<'a, T: ?Sized> {
    raw: &'a RawReentrantMutex,
    data: *const T,
    marker: PhantomData<&'a T>,
}

unsafe impl<'a, T: ?Sized + Sync + 'a> Sync
    for MappedReentrantMutexGuard<'a, T>
{
}

impl<'a, T: ?Sized + 'a>
    MappedReentrantMutexGuard<'a, T>
{
    /// Makes a new `MappedReentrantMutexGuard` for a component of the locked data.
    ///
    /// This operation cannot fail as the `MappedReentrantMutexGuard` passed
    /// in already locked the mutex.
    ///
    /// This is an associated function that needs to be
    /// used as `MappedReentrantMutexGuard::map(...)`. A method would interfere with methods of
    /// the same name on the contents of the locked data.
    #[inline]
    pub fn map<U: ?Sized, F>(s: Self, f: F) -> MappedReentrantMutexGuard<'a, U>
    where
        F: FnOnce(&T) -> &U,
    {
        let raw = s.raw;
        let data = f(unsafe { &*s.data });
        mem::forget(s);
        MappedReentrantMutexGuard {
            raw,
            data,
            marker: PhantomData,
        }
    }

    /// Attempts to make  a new `MappedReentrantMutexGuard` for a component of the
    /// locked data. The original guard is return if the closure returns `None`.
    ///
    /// This operation cannot fail as the `MappedReentrantMutexGuard` passed
    /// in already locked the mutex.
    ///
    /// This is an associated function that needs to be
    /// used as `MappedReentrantMutexGuard::map(...)`. A method would interfere with methods of
    /// the same name on the contents of the locked data.
    #[inline]
    pub fn try_map<U: ?Sized, F>(
        s: Self,
        f: F,
    ) -> Result<MappedReentrantMutexGuard<'a, U>, Self>
    where
        F: FnOnce(&T) -> Option<&U>,
    {
        let raw = s.raw;
        let data = match f(unsafe { &*s.data }) {
            Some(data) => data,
            None => return Err(s),
        };
        mem::forget(s);
        Ok(MappedReentrantMutexGuard {
            raw,
            data,
            marker: PhantomData,
        })
    }
}

impl<'a, T: ?Sized + 'a>
    MappedReentrantMutexGuard<'a, T>
{
    /// Unlocks the mutex using a fair unlock protocol.
    ///
    /// By default, mutexes are unfair and allow the current thread to re-lock
    /// the mutex before another has the chance to acquire the lock, even if
    /// that thread has been blocked on the mutex for a long time. This is the
    /// default because it allows much higher throughput as it avoids forcing a
    /// context switch on every mutex unlock. This can result in one thread
    /// acquiring a mutex many more times than other threads.
    ///
    /// However in some cases it can be beneficial to ensure fairness by forcing
    /// the lock to pass on to a waiting thread if there is one. This is done by
    /// using this method instead of dropping the `ReentrantMutexGuard` normally.
    #[inline]
    pub fn unlock_fair(s: Self) {
        s.raw.unlock_fair();
        mem::forget(s);
    }
}

impl<'a, T: ?Sized + 'a> Deref
    for MappedReentrantMutexGuard<'a, T>
{
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        unsafe { &*self.data }
    }
}

impl<'a, T: ?Sized + 'a> Drop
    for MappedReentrantMutexGuard<'a, T>
{
    #[inline]
    fn drop(&mut self) {
        self.raw.unlock();
    }
}

impl<'a, T: fmt::Debug + ?Sized + 'a> fmt::Debug
    for MappedReentrantMutexGuard<'a, T>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<'a, T: fmt::Display + ?Sized + 'a> fmt::Display
    for MappedReentrantMutexGuard<'a, T>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

#[cfg(feature = "owning_ref_support")]
unsafe impl<'a, T: ?Sized + 'a> StableAddress
    for MappedReentrantMutexGuard<'a, T>
{
}

#[cfg(test)]
mod tests {
    use crate::ReentrantMutex;
    use std::cell::RefCell;
    use std::sync::Arc;
    use std::thread;

    #[cfg(feature = "serde_support")]
    use bincode::{deserialize, serialize};

    #[test]
    fn smoke() {
        let m = ReentrantMutex::new(2);
        {
            let a = m.lock();
            {
                let b = m.lock();
                {
                    let c = m.lock();
                    assert_eq!(*c, 2);
                }
                assert_eq!(*b, 2);
            }
            assert_eq!(*a, 2);
        }
    }

    #[test]
    fn is_mutex() {
        let m = Arc::new(ReentrantMutex::new(RefCell::new(0)));
        let m2 = m.clone();
        let lock = m.lock();
        let child = thread::spawn(move || {
            let lock = m2.lock();
            assert_eq!(*lock.borrow(), 4950);
        });
        for i in 0..100 {
            let lock = m.lock();
            *lock.borrow_mut() += i;
        }
        drop(lock);
        child.join().unwrap();
    }

    #[test]
    fn trylock_works() {
        let m = Arc::new(ReentrantMutex::new(()));
        let m2 = m.clone();
        let _lock = m.try_lock();
        let _lock2 = m.try_lock();
        thread::spawn(move || {
            let lock = m2.try_lock();
            assert!(lock.is_none());
        })
        .join()
        .unwrap();
        let _lock3 = m.try_lock();
    }

    #[test]
    fn test_reentrant_mutex_debug() {
        let mutex = ReentrantMutex::new(vec![0u8, 10]);

        assert_eq!(format!("{:?}", mutex), "ReentrantMutex { data: [0, 10] }");
    }

    #[cfg(feature = "serde_support")]
    #[test]
    fn test_serde() {
        let contents: Vec<u8> = vec![0, 1, 2];
        let mutex = ReentrantMutex::new(contents.clone());

        let serialized = serialize(&mutex).unwrap();
        let deserialized: ReentrantMutex<Vec<u8>> = deserialize(&serialized).unwrap();

        assert_eq!(*(mutex.lock()), *(deserialized.lock()));
        assert_eq!(contents, *(deserialized.lock()));
    }
}
