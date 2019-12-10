/// A version of the locks from
/// [`parking_lot`](https://github.com/Amanieu/parking_lot) which can be used in
/// a static (e.g. without lazy_static, or OnceCell).
///
/// The only thing preventing this was the fact that the API was implemented in
/// a generic way in `lock_api`, and const trait bounds aren't fully supported
/// yet.
///
/// All this crate does is manually monomorphize (expand) the generic
/// implementation, allowing `Mutex::new`, `RwLock::new`, and
/// `ReentrantMutex::new`, etc to be used in statics. Eventually this will work
/// without this crate, at which point there will probably be no reason to use
/// it.
///
/// # Example:
///
/// ```
/// // Or RwLock, ReentrantMutex, ...
/// use static_locks::Mutex;
///
/// # struct MyType(String);
/// // Avoid lazy_static / OnceCell / and just use a static mutex!
/// static MUTEXED: Mutex<Option<MyType>> = Mutex::new(None);
/// ```
mod mutex;
mod remutex;
mod rwlock;
pub use mutex::*;
pub use remutex::*;
pub use rwlock::*;

/// Our version of parking_lot, re-exported should you need it.
pub use parking_lot;

// Used to avoid having to change the lock_api code where I don't need to. (It
// uses this crate too).
#[macro_use]
extern crate scopeguard;


#[cfg(test)]
mod test {
    use super::*;
    // Ensure we can make statics of these.
    #[allow(dead_code)]
    static MUTEXED: Mutex<()> = Mutex::new(());
    #[allow(dead_code)]
    static REMUTEXED: ReentrantMutex<()> = ReentrantMutex::new(());
    #[allow(dead_code)]
    static RWLOCKED: RwLock<()> = RwLock::new(());

    macro_rules! assert_impls_traits {
        ($ty:ty : $trait0:ident $(+ $trait_:ident)* $(,)?) => {{
            fn check<T: ?Sized + $trait0 $(+ $trait_)*>() {}
            check::<$ty>();
        }};
    }

    // ensure the parking lot types actually do implement what i assumed
    // they did when manually monomorphizing things.
    #[test]
    fn check_parkinglot_traits() {
        use parking_lot::lock_api::*;
        assert_impls_traits!(parking_lot::RawMutex: Send + Sync + RawMutexFair + RawMutexTimed);
        assert_impls_traits!(parking_lot::RawRwLock: Send + Sync + RawRwLock
            + RawRwLockFair + RawRwLockDowngrade + RawRwLockTimed + RawRwLockRecursive + RawRwLockRecursiveTimed
            + RawRwLockUpgrade + RawRwLockUpgradeFair + RawRwLockUpgradeDowngrade + RawRwLockUpgradeTimed);
    }
}
