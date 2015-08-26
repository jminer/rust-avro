
use std::borrow::Cow;
use std::collections::HashMap;

mod idl;



enum Value<'a> {
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

struct Field<'a> {
	name: Cow<'a, str>,
	doc: Option<Cow<'a, str>>,
	ty: Schema<'a>,
}

struct RecordSchema<'a> {
	name: Cow<'a, str>,
	doc: Option<Cow<'a, str>>,
	fields: Vec<Field<'a>>,
}

struct EnumSchema<'a> {
	name: Cow<'a, str>,
	doc: Option<Cow<'a, str>>,
	symbols: Vec<Cow<'a, str>>,
}

struct FixedSchema<'a> {
	name: Cow<'a, str>,
	doc: Option<Cow<'a, str>>,
	size: usize,
}

enum Schema<'a> {
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

struct Message<'a> {
	name: Cow<'a, str>,
	doc: Option<Cow<'a, str>>,
}

struct Protocol<'a> {
    name: Cow<'a, str>,
	doc: Option<Cow<'a, str>>,
    tys: Vec<Schema<'a>>,
    messages: Vec<Message<'a>>,
}
