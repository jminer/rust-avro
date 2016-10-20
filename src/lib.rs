/* Copyright 2015 Jordan Miner
 *
 * Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
 * http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
 * <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
 * option. This file may not be copied, modified, or distributed
 * except according to those terms.
 */

extern crate serde_json;

use std::borrow::Cow;
use std::collections::HashMap;
use std::rc::Rc;

mod idl;
mod decode;
mod encode;

pub use idl::Lexer;
pub use idl::IdlError;
pub use idl::parse_idl;
pub use decode::{
    DecodeError,
    DecodeErrorKind,
    decode,
    decode_var_len_u64,
    decode_zig_zag,
};
pub use encode::{
    encode_var_len_u64,
    encode_zig_zag,
    encode
};

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
	Map(HashMap<Cow<'b, str>, Value<'a, 'b>>),
	Fixed(Rc<FixedSchema<'a>>, Cow<'b, [u8]>),
}

macro_rules! value_unwrap_fn {
    ($n: ident, $t:ty, $variant:ident, $val_pat:pat => $ret:expr) => {
        pub fn $n(&self) -> $t {
            match self {
                $val_pat => $ret,
                _ => panic!(concat!(
                    "called `Value::", stringify!($n), "()` on a non-`", stringify!($variant), "` value: {:?}"), self),
            }
        }
    };
}

impl<'a, 'b> Value<'a, 'b> {
    value_unwrap_fn!(unwrap_boolean, bool, Boolean, &Value::Boolean(val) => val);
    value_unwrap_fn!(unwrap_int, i32, Int, &Value::Int(val) => val);
    value_unwrap_fn!(unwrap_long, i64, Long, &Value::Long(val) => val);
    value_unwrap_fn!(unwrap_float, f32, Float, &Value::Float(val) => val);
    value_unwrap_fn!(unwrap_double, f64, Double, &Value::Double(val) => val);
    value_unwrap_fn!(unwrap_bytes, &Cow<'b, [u8]>, Bytes, &Value::Bytes(ref val) => val);
    value_unwrap_fn!(unwrap_string, &Cow<'b, str>, String, &Value::String(ref val) => val);
    value_unwrap_fn!(unwrap_record, (&Rc<RecordSchema<'a>>, &Vec<Value<'a, 'b>>),
        Record, &Value::Record(ref sch, ref val) => (sch, val));
    value_unwrap_fn!(unwrap_enum, (&Rc<EnumSchema<'a>>, i32),
        Enum, &Value::Enum(ref sch, val) => (sch, val));
    value_unwrap_fn!(unwrap_array, &Vec<Value<'a, 'b>>, Array, &Value::Array(ref val) => val);
    value_unwrap_fn!(unwrap_map, &HashMap<Cow<'b, str>, Value<'a, 'b>>,
        Map, &Value::Map(ref val) => val);
    value_unwrap_fn!(unwrap_fixed, (&Rc<FixedSchema<'a>>, &Cow<'b, [u8]>),
        Fixed, &Value::Fixed(ref sch, ref val) => (sch, val));
}

#[test]
fn test_value_unwrap() {
    assert_eq!(Value::Boolean(true).unwrap_boolean(), true);
    assert_eq!(Value::Int(4).unwrap_int(), 4);
    assert_eq!(Value::Long(7).unwrap_long(), 7);
    assert_eq!(Value::Float(3.14).unwrap_float(), 3.14);
    assert_eq!(Value::Double(3.14).unwrap_double(), 3.14);
    assert_eq!(Value::Bytes(Cow::Borrowed(&b"hi"[..])).unwrap_bytes(), &Cow::Borrowed(&b"hi"[..]));
    assert_eq!(Value::String(Cow::Borrowed(&"hi"[..])).unwrap_string(), &Cow::Borrowed(&"hi"[..]));
}

#[derive(Debug, Clone, PartialEq)]
pub struct Property<'a> {
    pub name: Cow<'a, str>,
    pub value: serde_json::Value,
}

impl<'a> Property<'a> {
    pub fn new(name: Cow<'a, str>, value: serde_json::Value) -> Property {
        Property {
            name: name,
            value: value,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field<'a> {
	pub name: Cow<'a, str>,
	pub doc: Option<Cow<'a, str>>,
    pub properties: Vec<Property<'a>>,
	pub ty: Schema<'a>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordSchema<'a> {
	pub name: Cow<'a, str>,
	pub doc: Option<Cow<'a, str>>,
    pub properties: Vec<Property<'a>>,
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
    pub fn new(name: Cow<'a, str>,
               doc: Option<Cow<'a, str>>,
               properties: Vec<Property<'a>>,
               fields: Vec<Field<'a>>)
               -> RecordSchema<'a> {
        let indexes = create_field_indexes(&fields);
        RecordSchema {
            name: name,
            doc: doc,
            properties: properties,
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
    pub properties: Vec<Property<'a>>,
	pub symbols: Vec<EnumSymbol<'a>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FixedSchema<'a> {
	pub name: Cow<'a, str>,
	pub doc: Option<Cow<'a, str>>,
    pub properties: Vec<Property<'a>>,
	pub size: usize,
}

impl<'a> FixedSchema<'a> {
    pub fn new(name: Cow<'a, str>,
               doc: Option<Cow<'a, str>>,
               properties: Vec<Property<'a>>,
               size: usize)
               -> FixedSchema<'a> {
        FixedSchema {
            name: name,
            properties: properties,
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
    pub properties: Vec<Property<'a>>,
    pub tys: Vec<Schema<'a>>,
    pub messages: Vec<Message<'a>>,
}
