// Configure Vec/allocation imports based on features.
// We implement a common api depending on the nightly/allocator-api2
// features, which is consumed uniformly by the impls.
pub use _impl_::*;

// If not on nightly, and no allocator-api2 enabled, use a normal alloc::Vec.
// This should be the same behavior as before the features were added.
#[cfg(not(any(feature = "nightly", feature = "allocator-api2")))]
mod _impl_ {
    pub use alloc::collections::TryReserveError;
    pub use alloc::vec::Vec;
    use core::marker::PhantomData;
    use core::ops::{Deref, DerefMut};

    pub trait Allocator {}
    #[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
    pub struct Global;
    impl Allocator for Global {}

    #[repr(transparent)]
    #[derive(Debug, Clone)]
    pub struct VecWrap<T, A: Allocator = Global>(alloc::vec::Vec<T>, PhantomData<A>);

    impl<T, A: Allocator> VecWrap<T, A> {
        #[inline(always)]
        pub fn wrap(inner: alloc::vec::Vec<T>) -> Self {
            Self(inner, PhantomData)
        }
        #[inline(always)]
        pub fn try_with_capacity_in(
            capacity: usize,
            _allocator: A,
        ) -> Result<Self, TryReserveError> {
            Ok(Self::wrap(Vec::with_capacity(capacity)))
        }
    }

    impl<T, A: Allocator> Deref for VecWrap<T, A> {
        type Target = alloc::vec::Vec<T>;
        #[inline(always)]
        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl<T, A: Allocator> DerefMut for VecWrap<T, A> {
        #[inline(always)]
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.0
        }
    }

    impl<T, A: Allocator> IntoIterator for VecWrap<T, A> {
        type Item = <<Self as Deref>::Target as IntoIterator>::Item;
        type IntoIter = <<Self as Deref>::Target as IntoIterator>::IntoIter;
        #[inline(always)]
        fn into_iter(self) -> Self::IntoIter {
            self.0.into_iter()
        }
    }

    #[repr(transparent)]
    #[derive(Debug, Clone)]
    pub struct VecIntoIterWrap<T, A: Allocator = Global>(alloc::vec::IntoIter<T>, PhantomData<A>);
    impl<T, A: Allocator> VecIntoIterWrap<T, A> {
        #[inline(always)]
        pub fn wrap(inner: alloc::vec::IntoIter<T>) -> Self {
            Self(inner, PhantomData)
        }
    }

    impl<T, A: Allocator> Iterator for VecIntoIterWrap<T, A> {
        type Item = <alloc::vec::IntoIter<T> as Iterator>::Item;
        #[inline(always)]
        fn next(&mut self) -> Option<Self::Item> {
            self.0.next()
        }
    }
}

// If on nightly: Use nightly allocator_api
#[cfg(feature = "nightly")]
mod _impl_ {
    #[cfg(test)]
    pub use alloc::alloc::AllocError;
    pub use alloc::alloc::{Allocator, Global};
    pub use alloc::collections::TryReserveError;
    pub use alloc::vec::Vec;
    use core::ops::{Deref, DerefMut};

    #[repr(transparent)]
    #[derive(Debug, Clone)]
    pub struct VecWrap<T, A: Allocator = Global>(alloc::vec::Vec<T, A>);

    impl<T, A: Allocator> VecWrap<T, A> {
        #[inline(always)]
        pub fn wrap(inner: alloc::vec::Vec<T, A>) -> Self {
            Self(inner)
        }
        #[inline(always)]
        pub fn try_with_capacity_in(
            capacity: usize,
            allocator: A,
        ) -> Result<Self, TryReserveError> {
            Ok(Self::wrap(Vec::try_with_capacity_in(capacity, allocator)?))
        }
    }

    impl<T, A: Allocator> Deref for VecWrap<T, A> {
        type Target = alloc::vec::Vec<T, A>;
        #[inline(always)]
        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl<T, A: Allocator> DerefMut for VecWrap<T, A> {
        #[inline(always)]
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.0
        }
    }

    impl<T, A: Allocator> IntoIterator for VecWrap<T, A> {
        type Item = <<Self as Deref>::Target as IntoIterator>::Item;
        type IntoIter = <<Self as Deref>::Target as IntoIterator>::IntoIter;
        #[inline(always)]
        fn into_iter(self) -> Self::IntoIter {
            self.0.into_iter()
        }
    }

    #[repr(transparent)]
    #[derive(Debug, Clone)]
    pub struct VecIntoIterWrap<T, A: Allocator = Global>(alloc::vec::IntoIter<T, A>);
    impl<T, A: Allocator> VecIntoIterWrap<T, A> {
        #[inline(always)]
        pub fn wrap(inner: alloc::vec::IntoIter<T, A>) -> Self {
            Self(inner)
        }
    }

    impl<T, A: Allocator> Iterator for VecIntoIterWrap<T, A> {
        type Item = <alloc::vec::IntoIter<T, A> as Iterator>::Item;
        #[inline(always)]
        fn next(&mut self) -> Option<Self::Item> {
            self.0.next()
        }
    }
}

// If not on nightly, but allocator-api2 is enabled: use it
#[cfg(all(not(feature = "nightly"), feature = "allocator-api2"))]
mod _impl_ {
    use core::ops::{Deref, DerefMut};

    #[cfg(test)]
    pub use allocator_api2::alloc::AllocError;
    pub use allocator_api2::alloc::{Allocator, Global};
    pub use allocator_api2::collections::TryReserveError;
    pub use allocator_api2::vec::Vec;

    #[repr(transparent)]
    #[derive(Debug, Clone)]
    pub struct VecWrap<T, A: Allocator = Global>(allocator_api2::vec::Vec<T, A>);

    impl<T, A: Allocator> VecWrap<T, A> {
        #[inline(always)]
        pub fn wrap(inner: allocator_api2::vec::Vec<T, A>) -> Self {
            Self(inner)
        }
        #[inline(always)]
        pub fn try_with_capacity_in(
            capacity: usize,
            allocator: A,
        ) -> Result<Self, TryReserveError> {
            // try_with_capacity_in is unstable, so we emulate it with a try_reserve when not on nightly
            let mut vec = Vec::new_in(allocator);
            vec.try_reserve(capacity)?;
            Ok(VecWrap::wrap(vec))
        }
    }

    impl<T, A: Allocator> Deref for VecWrap<T, A> {
        type Target = allocator_api2::vec::Vec<T, A>;
        #[inline(always)]
        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl<T, A: Allocator> DerefMut for VecWrap<T, A> {
        #[inline(always)]
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.0
        }
    }

    impl<T, A: Allocator> IntoIterator for VecWrap<T, A> {
        type Item = <<Self as Deref>::Target as IntoIterator>::Item;
        type IntoIter = <<Self as Deref>::Target as IntoIterator>::IntoIter;
        fn into_iter(self) -> Self::IntoIter {
            self.0.into_iter()
        }
    }

    #[repr(transparent)]
    #[derive(Debug, Clone)]
    pub struct VecIntoIterWrap<T, A: Allocator = Global>(allocator_api2::vec::IntoIter<T, A>);
    impl<T, A: Allocator> VecIntoIterWrap<T, A> {
        #[inline(always)]
        pub fn wrap(inner: allocator_api2::vec::IntoIter<T, A>) -> Self {
            Self(inner)
        }
    }

    impl<T, A: Allocator> Iterator for VecIntoIterWrap<T, A> {
        type Item = <allocator_api2::vec::IntoIter<T, A> as Iterator>::Item;
        #[inline(always)]
        fn next(&mut self) -> Option<Self::Item> {
            self.0.next()
        }
    }
}
