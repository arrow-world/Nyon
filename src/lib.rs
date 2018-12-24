#![allow(non_snake_case)]
#![recursion_limit = "1024"]

mod current;
mod signal;
mod dns;
pub mod syntax;

// extern crate llvm_sys;
// extern crate rustc_llvm_proxy;
extern crate combine;
extern crate num;
extern crate unicode_categories;

#[cfg(test)]
mod tests {
}