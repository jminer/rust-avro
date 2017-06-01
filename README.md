
# Avro for Rust

An implementation of Avro for Rust.

    [dependencies]
    avro = { git = "https://github.com/jminer/rust-avro" }

[Documentation](http://jminer.github.io/rust-avro/avro/index.html)

## Status

My motivation for this project is decoding binary log messages sent from a C application. Rather than invent a new format, I started a general Avro library. Therefore, there isn't yet support for reading JSON protocol (.avpr) files or encoding Avro data. Features:

- Partial IDL protocol file (.avdl) parsing (notably lacking is messages or reference types)
- Partial decoding support (lacking reference types, like the IDL file parsing)

I'd like to see support for more Avro features in the future.

# Compatibility tests

This library has some tests that it is compatible with the Java Avro implementation (which I think is the reference implementation). The tests require that Java is installed. For this reason, they are disabled by default; running `cargo test` will not run them. To run them, you must run `cargo test --feature java-compat`. The first time one of the tests is run, it will download the compiled Java implementation of Avro.
