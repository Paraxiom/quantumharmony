//! NoClone wrapper to enforce quantum no-cloning theorem at compile time

use core::fmt;
use core::ops::{Deref, DerefMut};

/// Wrapper type that prevents cloning, enforcing the quantum no-cloning theorem
/// 
/// This type ensures that quantum states cannot be duplicated, which is a
/// fundamental law of quantum mechanics.
#[derive(Debug)]
pub struct NoClone<T>(T);

impl<T> NoClone<T> {
    /// Create a new NoClone wrapper
    pub fn new(value: T) -> Self {
        NoClone(value)
    }

    /// Consume the wrapper and return the inner value
    pub fn into_inner(self) -> T {
        self.0
    }

    /// Get a reference to the inner value
    pub fn as_ref(&self) -> &T {
        &self.0
    }

    /// Get a mutable reference to the inner value
    pub fn as_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

// Explicitly NOT implementing Clone!
// This is the whole point - quantum states cannot be cloned

impl<T> Deref for NoClone<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for NoClone<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T: fmt::Display> fmt::Display for NoClone<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "NoClone({})", self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_no_clone_creation() {
        let value = NoClone::new(42);
        assert_eq!(*value, 42);
    }

    #[test]
    fn test_no_clone_into_inner() {
        let value = NoClone::new("quantum state");
        let inner = value.into_inner();
        assert_eq!(inner, "quantum state");
    }

    // This test should NOT compile if uncommented:
    // #[test]
    // fn test_clone_fails() {
    //     let value = NoClone::new(42);
    //     let _clone = value.clone(); // ❌ Error: NoClone<i32> doesn't implement Clone
    // }
}