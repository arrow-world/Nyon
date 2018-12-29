#![allow(non_snake_case)]
#![recursion_limit = "2048"]

pub mod syntax;
mod env;
mod idgen;

extern crate combine;
extern crate num;
extern crate unicode_categories;

#[cfg(test)]
mod tests {
}