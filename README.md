# Daiyatsu
A CLR1 parser generator made in Rust

## Features

For testing right now we have macros that allow us to write grammars like:

```rust
make_grammar![
    "expr" : "atom" "+" "atom" | "atom" "-" "atom"
    ,"atom": "Nat" | "(" "expr" ")"
]
```

And it automatically translate that to the internal representation.
We plan to develop a full format for grammars out of rust files,
but this is nice enough that we may end keeping this feature in the
public API.

## Specification

The grammar for Daiyatsu is a combination of various things:

- Is based on EBNF
- Has macro declarations
- Has a lexer integrated

Our main goal is to take a grammar like this

```lark
%macro sep_by1{rule,separator} : (rule separator)* separator;
%macro between{start,rule,end} : start rule end;
%macro list_macro{start,item,separator,end} : between{start,sep_by1{item,separator},end}

Identifier : /[a-z][a-zA-Z_0-9]*/

list_inner : Uint
list : list_macro{"[",list_inner,",","]"}

record_inner : Identifier ":" Identifier
record : list_macro{"{",list_inner,",` ","}"}

imports : list_macro{"(",Identifier,",",")"}
    | sep_by1{Identifier,","} ";"
import : "from" Identifier "import" imports

all : (list | record | import)*
```

Then transform it to a BNF grammar internally in a way that we can map the
BNF error messages to the original version.

### Notation

In this specification we are going to use EBNF to describe Daiyatsu grammar.

- `CammelCase` identifiers denote tokens.
- `snake_case` identifiers denote non terminals.


### Regular expression

A regular expression is a Rust regular expression surrounded by delimiters

```ebnf
regular_expression : "/" RustRegularExpression "/"
    | "<" RustRegularExpression ">"
    | "</" RustRegularExpression "/>"
```

The delimiters arent clear at the moment


### Comments

#### Line comment

### Tokens

Tokens start with uppercase letters and are followed by its definition

```ebnf
TokenIdentifier : UpercaseLetter (Letter|Digit|"_")*
token_declaration : TokenIdentifier ":" (regular_expression|TokenIdentifier|TokenLiteral)+
```




## Develop

- The core file right now is in the file `grammar.rs`


## Roadmap

### Core
- [X] Core grammar definitions.
- [X] Find nullable rules.
- [X] Find first sets (add more test).
- [ ] Find follow sets.
- [ ] Find set closure.
- [ ] Generate parsing tables.
- [ ] Generate parsers with generic trees dynamically.
- [ ] Write code generator.

### Front-end
- [ ] Define a grammar for Daiyatsu (in progress).
- [ ] Create a Tree sitter grammar for Daiyatsu (in progress).
- [ ] Define a CST and AST for Daiyatsu grammar.
- [ ] Daiyatsu grammar formatter.
- [ ] Daiyatsu simple LSP (just reparse file on change).
- [ ] Daiyatsu LSP with persistent tree.
- [ ] Add module system.

### Future
- [ ] Image generation.
- [ ] Web browser try me.
- [ ] LL(k) parser.
- [ ] GLR(1)?
