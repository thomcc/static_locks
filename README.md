# `static_locks`

The [`parking_lot`](https://github.com/Amanieu/parking_lot) locks but modified
so that they can be used in statics on stable Rust.

The only thing preventing this was the fact that the API was implemented in a
generic way in `lock_api`, and const trait bounds aren't fully supported yet.
All this crate does is manually monomorphize (expand) the generic
implementation, allowing `Mutex::new`, `RwLock::new`, and `ReentrantMutex::new`,
etc to be used in statics.

It essentially exists so that you don't have to use a lazy_static or OnceCell
for in cases where you shouldn't.

## Caveats

1. Can't use our `MutexGuard` with `Condvar` from normal `parking_lot`.
2. Some features have been renamed, e.g. serde => serde_support, in order to
   meet cargos rule about not having a feature && dep of the same name.
3. Doesn't contain things from parking_lot other than the locks, although we do
   reexport the parking lot crate, e.g. `static_locks::parking_lot::{...}`
   is available.
4.

# License

Same as `parking_lot`, down to the copyright attribution. The author of
`stable_locks` claims no additional copyright over the changes to the
parking_lot code needed -- They were trivial.
