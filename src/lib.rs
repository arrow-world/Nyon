#![allow(non_snake_case)]
#![recursion_limit = "2048"]

pub mod syntax;
pub mod core;

extern crate combine;
extern crate num;
extern crate unicode_categories;

#[macro_use] extern crate log;

#[cfg(test)]
mod tests {
}