# MiniSheet

MiniSheet is a batch program for evaluating a "spreadsheet" in csv format.
The project is just an excercise.
For now only vertical bars are allowed as delimiters.

## Quick Start

```console
cargo run -- input.csv
```
or
```console
cargo run -- input.csv output.csv
```

Example input:
```csv
column 1 | column 2
-10      | 2
3        | 4
=B4+10   | =A3*A2 
```

Output:
```csv
 column 1 | column 2
 -10 | 2
 3 | 4
 -20 | -30
```
