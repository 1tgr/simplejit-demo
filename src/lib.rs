#[macro_export]
macro_rules! error {
    ($msg:literal) => {
        $crate::Error::new(anyhow::anyhow!($msg))
    };
    ($msg:expr) => {
        $crate::Error::new(anyhow::anyhow!($msg))
    };
    ($fmt:expr, $($arg:tt)*) => {
        $crate::Error::new(anyhow::anyhow!($fmt, $($arg)*))
    };
}

#[macro_export]
macro_rules! ensure {
    ($cond:expr) => {
        if !$cond {
            return Err(error!(concat!("check failed: ", stringify!($cond))));
        }
    };
    ($cond:expr, $msg:literal) => {
        if !$cond {
            return Err(error!($msg));
        }
    };
    ($cond:expr, $fmt:expr, $($arg:tt)*) => {
        if !$cond {
            return Err(error!($fmt, $($arg)*));
        }
    };
}

#[macro_export]
macro_rules! ensure_eq {
    ($lhs:expr, $rhs:expr) => {
        ensure!($lhs == $rhs);
    };
    ($lhs:expr, $rhs:expr, $($arg:tt)*) => {
        ensure!($lhs == $rhs, $($arg)*);
    };
}

pub mod ast;
pub mod frontend;

mod database;
mod intern;
mod jit;
mod lower;
mod parse;
mod pretty;
mod source;
mod target;
mod type_ck;
mod unify;

#[cfg(test)]
mod tests;

use derive_more::Display;
use std::error;
use std::fmt;
use std::rc::Rc;
use std::result;

#[derive(Clone, Display)]
#[display(fmt = "{}", "_0")]
pub struct Error(Rc<anyhow::Error>);

impl Error {
    pub fn new(error: anyhow::Error) -> Self {
        Self(Rc::new(error))
    }
}

impl<E> From<E> for Error
where
    E: error::Error + Send + Sync + 'static,
{
    fn from(error: E) -> Self {
        Self::new(anyhow::Error::new(error))
    }
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl PartialEq for Error {
    #[allow(clippy::vtable_address_comparisons)]
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for Error {}

pub type Result<T> = result::Result<T, Error>;

trait VecExt<T> {
    fn into_single_item(self) -> result::Result<T, Self>
    where
        Self: Sized;

    fn as_single_item(&mut self) -> Option<T>;
}

impl<T> VecExt<T> for Vec<T> {
    fn into_single_item(mut self) -> result::Result<T, Self> {
        if let Some(item) = self.pop() {
            if self.is_empty() {
                return Ok(item);
            }

            self.push(item);
        }

        Err(self)
    }

    fn as_single_item(&mut self) -> Option<T> {
        if let Some(item) = self.pop() {
            if self.is_empty() {
                return Some(item);
            }

            self.push(item);
        }

        None
    }
}

pub use database::Database;
pub use intern::{Intern, InternExt};
pub use jit::{Context, JIT};
pub use lower::Lower;
pub use parse::Parse;
pub use pretty::{PrettyExt, PrettyPrintExpr, PrettyPrintFunction, PrettyPrintType};
pub use source::Source;
pub use target::{Target, TargetExt};
pub use type_ck::TypeCk;
