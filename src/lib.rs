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
use std::rc::Rc;

mod idl;
mod decode;

pub use idl::Lexer;
pub use idl::parse_idl;
pub use decode::decode;

#[derive(Debug, Clone, PartialEq)]
pub enum Value<'a, 'b> {
	Null,
	Boolean(bool),
	Int(i32),
	Long(i64),
	Float(f32),
	Double(f64),
	Bytes(Cow<'b, [u8]>),
	String(Cow<'b, str>),
	Record(Rc<RecordSchema<'a>>, Vec<Value<'a, 'b>>),
	Enum(Rc<EnumSchema<'a>>, i32),
	Array(Vec<Value<'a, 'b>>),
	Map(HashMap<Cow<'a, str>, Value<'a, 'b>>),
	Fixed(Rc<FixedSchema<'a>>, Cow<'b, [u8]>),

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
	pub field_indexes: HashMap<Cow<'a, str>, usize>,
}

fn create_field_indexes<'a>(fields: &Vec<Field<'a>>) -> HashMap<Cow<'a, str>, usize> {
    fields.iter().enumerate().fold(HashMap::new(), |mut map, (i, f)| {
        map.insert(f.name.clone(), i);
        map
    })
}

impl<'a> RecordSchema<'a> {
    pub fn new(name: Cow<'a, str>, doc: Option<Cow<'a, str>>, fields: Vec<Field<'a>>)
    -> RecordSchema<'a> {
        let indexes = create_field_indexes(&fields);
        RecordSchema {
            name: name,
            doc: doc,
            fields: fields,
            field_indexes: indexes,
        }
    }
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

impl<'a> FixedSchema<'a> {
    pub fn new(name: Cow<'a, str>, doc: Option<Cow<'a, str>>, size: usize)
    -> FixedSchema<'a> {
        FixedSchema {
            name: name,
            doc: doc,
            size: size,
        }
    }
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
	Record(Rc<RecordSchema<'a>>),
	Error(Rc<RecordSchema<'a>>),
	Enum(Rc<EnumSchema<'a>>),
	Array {
		items: Box<Schema<'a>>,
	},
	Map {
		values: Box<Schema<'a>>,
	},
	Union {
		tys: Vec<Schema<'a>>,
	},
	Fixed(Rc<FixedSchema<'a>>),
}

//impl<'a> Schema<'a> {
//    pub fn to_static(&self) -> Schema<'static> {
//    }
//}

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
