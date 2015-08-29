
# Avro for Rust

An implementation of Avro for Rust.

    [dependencies]
    avro = { git = "https://github.com/jminer/rust-avro" }

## Status

My motivation for this project is decoding binary log messages sent from a C application. Rather than invent a new format, I started a general Avro library. Therefore, there isn't yet support for reading JSON protocol (.avpr) files or encoding Avro data. Features:

- Partial IDL protocol file (.avdl) parsing (no support for annotations or messages)

I'd like to see support for more Avro features in the future.