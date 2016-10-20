/* Copyright 2016 Jordan Miner
 *
 * Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
 * http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
 * <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
 * option. This file may not be copied, modified, or distributed
 * except according to those terms.
 */

use std::io;
use std::io::Write;
use std::mem;
use Value;
use Schema;

#[derive(Debug)]
pub enum EncodeErrorKind {
    WriteFailed(io::Error),
    InvalidSchema,
}

#[derive(Debug)]
pub struct EncodeError {
    pub kind: EncodeErrorKind,
}

impl From<io::Error> for EncodeError {
    fn from(err: io::Error) -> EncodeError {
        EncodeError { kind: EncodeErrorKind::WriteFailed(err) }
    }
}

pub fn encode_var_len_u64<W: Write>(writer: &mut W, mut num: u64) -> Result<(), EncodeError> {
    loop {
        let mut b = (num & 0b0111_1111) as u8;
        num >>= 7;
        if num == 0 {
            try!(writer.write(&[b]));
            break;
        }
        b |= 0b1000_0000;
        try!(writer.write(&[b]));
    }
    Ok(())
}

#[test]
fn test_encode_var_len_u64() {
    let mut vec = vec![];

    encode_var_len_u64(&mut vec, 3).unwrap();
    assert_eq!(&vec, &b"\x03");
    vec.clear();

    encode_var_len_u64(&mut vec, 128).unwrap();
    assert_eq!(&vec, &b"\x80\x01");
    vec.clear();

    encode_var_len_u64(&mut vec, 130).unwrap();
    assert_eq!(&vec, &b"\x82\x01");
    vec.clear();

    encode_var_len_u64(&mut vec, 944261).unwrap();
    assert_eq!(&vec, &b"\x85\xD1\x39");
    vec.clear();
}

pub fn encode_zig_zag(num: i64) -> u64 {
    // compiles to (num << 1) ^ (num >> 63)
    if num < 0 {
        !((num as u64) << 1)
    } else {
        (num as u64) << 1
    }
}

#[test]
fn test_encode_zig_zag() {
    assert_eq!(encode_zig_zag(0), 0);
    assert_eq!(encode_zig_zag(-1), 1);
    assert_eq!(encode_zig_zag(1), 2);
    assert_eq!(encode_zig_zag(-2), 3);
    assert_eq!(encode_zig_zag(i64::min_value()), 0xFFFFFFFF_FFFFFFFF);
    assert_eq!(encode_zig_zag(i64::max_value()), 0xFFFFFFFF_FFFFFFFE); // 0x7FFF...FF
}

pub fn encode<W: Write>(writer: &mut W, schema: &Schema, value: &Value) -> Result<(), EncodeError> {
    match (schema, value) {
        (&Schema::Null, &Value::Null) => Ok(()),
        (&Schema::Null, _)            => Err(EncodeError { kind: EncodeErrorKind::InvalidSchema }),

        (&Schema::Boolean, &Value::Boolean(true))  => { try!(writer.write(&[0x01])); Ok(()) },
        (&Schema::Boolean, &Value::Boolean(false)) => { try!(writer.write(&[0x00])); Ok(()) },
        (&Schema::Boolean, _) => Err(EncodeError { kind: EncodeErrorKind::InvalidSchema }),

        (&Schema::Int, &Value::Int(num)) => {
            encode_var_len_u64(writer, encode_zig_zag(num as i64))
        },
        (&Schema::Int, _) => Err(EncodeError { kind: EncodeErrorKind::InvalidSchema }),

        (&Schema::Long, &Value::Long(num)) => {
            encode_var_len_u64(writer, encode_zig_zag(num))
        },
        (&Schema::Long, _) => Err(EncodeError { kind: EncodeErrorKind::InvalidSchema }),

        (&Schema::Float, &Value::Float(num)) => {
            let buf: [u8; 4] = unsafe { mem::transmute(num) };
            try!(writer.write(&buf));
            Ok(())
        },
        (&Schema::Float, _) => Err(EncodeError { kind: EncodeErrorKind::InvalidSchema }),

        (&Schema::Double, &Value::Double(num)) => {
            let buf: [u8; 8] = unsafe { mem::transmute(num) };
            try!(writer.write(&buf));
            Ok(())
        },
        (&Schema::Double, _) => Err(EncodeError { kind: EncodeErrorKind::InvalidSchema }),

        (&Schema::String, &Value::String(ref string)) => {
            try!(encode(writer, &Schema::Long, &Value::Long(string.len() as i64)));
            try!(writer.write(string.as_bytes()));
            Ok(())
        },
        (&Schema::String, _) => Err(EncodeError { kind: EncodeErrorKind::InvalidSchema }),

        (&Schema::Enum(ref inner_schema), &Value::Enum(ref value_schema, num)) => {
            try!(encode(writer, &Schema::Int, &Value::Int(num as i32)));
            Ok(())
        },
        (&Schema::Enum(_), _) => Err(EncodeError { kind: EncodeErrorKind::InvalidSchema }),

        //Schema::Array { items } => ,
        //Schema::Map { values } => ,
        //Schema::Union { tys } => ,
        (&Schema::Record(ref inner_schema), &Value::Record(ref value_schema, ref fields)) => {
            for (field, value) in value_schema.fields.iter().zip(fields.iter()) {
                try!(encode(writer, &field.ty, value));
            }
            Ok(())
        },

        _ => unimplemented!(),
    }
}

#[test]
fn test_encode_ints() {
    let mut vec = vec![];

    encode(&mut vec, &Schema::Int, &Value::Int(2)).unwrap();
    assert_eq!(&vec, &b"\x04");
    vec.clear();

    encode(&mut vec, &Schema::Int, &Value::Int(130)).unwrap();
    assert_eq!(&vec, &b"\x84\x02");
    vec.clear();

    encode(&mut vec, &Schema::Int, &Value::Int(-130)).unwrap();
    assert_eq!(&vec, &b"\x83\x02");
    vec.clear();

    encode(&mut vec, &Schema::Long, &Value::Long(130)).unwrap();
    assert_eq!(&vec, &b"\x84\x02");
    vec.clear();
}

#[test]
fn test_encode_floats() {
    let mut vec = vec![];

    encode(&mut vec, &Schema::Float, &Value::Float(0.0)).unwrap();
    assert_eq!(&vec, &b"\x00\x00\x00\x00");
    vec.clear();

    encode(&mut vec, &Schema::Float, &Value::Float(3.14)).unwrap();
    assert_eq!(&vec, &b"\xC3\xF5\x48\x40");
    vec.clear();

    encode(&mut vec, &Schema::Double, &Value::Double(2.718)).unwrap();
    assert_eq!(&vec, &b"\x58\x39\xB4\xC8\x76\xBE\x05\x40");
    vec.clear();
}

#[test]
fn test_encode_string() {
    let mut vec = vec![];

    encode(&mut vec, &Schema::String, &Value::String("yes".into())).unwrap();
    assert_eq!(&vec, &b"\x06\x79\x65\x73");
    vec.clear();
}


#[test]
fn test_encode_record() {
    use std::rc::Rc;
    use super::{Field, RecordSchema};

    let fields = vec![
        Field { name: "year".into(), doc: None, properties: vec![], ty: Schema::Int },
        Field { name: "color".into(), doc: None, properties: vec![], ty: Schema::String },
        Field { name: "running".into(), doc: None, properties: vec![], ty: Schema::Boolean },
    ];
    let schema = Rc::new(RecordSchema::new("Car".into(), None, vec![], fields));
    let value = Value::Record(schema.clone(), vec![
        Value::Int(2007),
        Value::String("Red".into()),
        Value::Boolean(true)
    ]);
    let mut vec = vec![];
    encode(&mut vec, &Schema::Record(schema), &value);

    assert_eq!(&vec, &b"\xAE\x1F\x06\x52\x65\x64\x01");
    vec.clear();
}
