#![allow(non_snake_case)]
#![recursion_limit = "2048"]

pub mod syntax;
pub mod core;

extern crate combine;
extern crate num;
extern crate unicode_categories;

extern crate serde;
#[macro_use] extern crate serde_derive;
extern crate rmp_serde;

#[macro_use] extern crate log;

#[cfg(test)]
mod tests {
}