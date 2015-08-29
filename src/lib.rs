/* Copyright 2015 Jordan Miner
 *
 * Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
 * http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
 * <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
 * option. This file may not be copied, modified, or distributed
 * except according to those terms.
 */

use std::borrow::Cow;
use std::collections::HashMap;

mod idl;

pub use idl::Lexer;
pub use idl::parse_idl;

#[derive(Debug, Clone, PartialEq)]
pub enum Value<'a> {
	Null,
	Boolean,
	Int(i32),
	Long(i64),
	Float(f32),
	Double(f64),
	Bytes(Cow<'a, [u8]>),
	String(Cow<'a, str>),
	Record(RecordSchema<'a>, HashMap<Cow<'a, str>, Value<'a>>), // should this be Vec instead?
	Enum(EnumSchema<'a>, i32),
	Array(Vec<Value<'a>>),
	Map(HashMap<Cow<'a, str>, Value<'a>>),
	Fixed(FixedSchema<'a>, Cow<'a, [u8]>),

}

#[derive(Debug, Clone, PartialEq)]
pub struct Field<'a> {
	pub name: Cow<'a, str>,
	pub doc: Option<Cow<'a, str>>,
	pub ty: Schema<'a>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordSchema<'a> {
	pub name: Cow<'a, str>,
	pub doc: Option<Cow<'a, str>>,
	pub fields: Vec<Field<'a>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumSymbol<'a> {
	pub name: Cow<'a, str>,
	pub doc: Option<Cow<'a, str>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumSchema<'a> {
	pub name: Cow<'a, str>,
	pub doc: Option<Cow<'a, str>>,
	pub symbols: Vec<EnumSymbol<'a>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FixedSchema<'a> {
	pub name: Cow<'a, str>,
	pub doc: Option<Cow<'a, str>>,
	pub size: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Schema<'a> {
	Null,
	Boolean,
	Int,
	Long,
	Float,
	Double,
	Bytes,
	String,
	Record(Box<RecordSchema<'a>>),
	Error(Box<RecordSchema<'a>>),
	Enum(Box<EnumSchema<'a>>),
	Array {
		items: Box<Schema<'a>>,
	},
	Map {
		values: Box<Schema<'a>>,
	},
	Union {
		tys: Vec<Schema<'a>>,
	},
	Fixed(Box<FixedSchema<'a>>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Message<'a> {
	pub name: Cow<'a, str>,
	pub doc: Option<Cow<'a, str>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Protocol<'a> {
    pub name: Cow<'a, str>,
	pub doc: Option<Cow<'a, str>>,
    pub tys: Vec<Schema<'a>>,
    pub messages: Vec<Message<'a>>,
}
