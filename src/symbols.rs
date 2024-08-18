use std::{
    collections::{HashMap, HashSet},
    sync::LazyLock,
};

static EOF_STRING: LazyLock<String> = LazyLock::new(|| String::from("Eof"));
static EMPTY_STRING: LazyLock<String> = LazyLock::new(|| String::from("Empty"));

/// Originally we used [usize] alone, but this is more explicit
/// about [Symbol::Eof] and [Symbol::Empty], aditionally
/// we parameterize over [IdType] to reuse Symbol outside.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy)]
pub enum Symbol {
    /// Token for end of the file.
    Eof,
    /// The empty character (token), we treat other tokens
    /// as not empty
    Empty,
    /// Regular tokens/non terminals.
    Id(usize),
}

impl Symbol {
    pub fn is_empty(&self) -> bool {
        match self {
            Symbol::Empty => true,
            _ => false,
        }
    }

    pub fn to_string(self, symbols: &Vec<String>) -> Option<String> {
        match self {
            Symbol::Id(name_id) => match symbols.get(name_id) {
                Some(name) => Some(name.clone()),
                None => None,
            },
            Symbol::Eof => Some(String::from("Eof")),
            Symbol::Empty => Some(String::from("Empty")),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct SymbolsRegistry {
    vec: Vec<String>,
    dic: HashMap<String, usize>,
}

impl SymbolsRegistry {
    /// The register together with the set of grammar rules
    /// transformed as a vector.
    pub fn make(
        raw: &HashMap<String, Vec<Vec<String>>>,
    ) -> (SymbolsRegistry, Vec<Vec<Vec<Symbol>>>) {
        let mut r = SymbolsRegistry {
            vec: vec![],
            dic: HashMap::new(),
        };
        let mut v: Vec<Vec<Vec<String>>> = vec![];
        // First, get the right index for non terminals
        // This is important since grammar expects us
        // to provide only the non terminals and consider all
        // other symbols as terminals.
        // we want to guarantee the order of the elements of v.
        for (name, rule) in raw {
            r.insert(name);
            v.push(rule.clone());
        }
        let out = v
            .into_iter()
            .map(|rule| {
                rule.into_iter()
                    .map(|production| {
                        production
                            .into_iter()
                            .map(|name| r.insert(&name))
                            .collect()
                    })
                    .collect()
            })
            .collect();
        (r, out)
    }

    pub fn is_empty_string(s: &str) -> bool {
        s == *EMPTY_STRING
    }

    pub fn is_eof_string(s: &str) -> bool {
        s == *EOF_STRING
    }

    pub fn insert(&mut self, s: &String) -> Symbol {
        match self.solve_name(s) {
            Some(name_id) => name_id,
            None => {
                let index = self.vec.len();
                self.vec.push(s.clone());
                self.dic.insert(s.clone(), index);
                Symbol::Id(index)
            }
        }
    }

    pub fn solve_name(&self, name: &String) -> Option<Symbol> {
        if Self::is_empty_string(name) {
            Some(Symbol::Empty)
        } else if Self::is_eof_string(name) {
            Some(Symbol::Eof)
        } else {
            let result = self.dic.get(name)?;
            Some(Symbol::Id(*result))
        }
    }

    pub fn solve_id(&self, name_id: usize) -> Option<&String> {
        self.vec.get(name_id)
    }

    pub fn solve_symbol(&self, symbol: Symbol) -> Option<&String> {
        match symbol {
            Symbol::Eof => Some(&EOF_STRING),
            Symbol::Empty => Some(&EMPTY_STRING),
            Symbol::Id(name_id) => self.vec.get(name_id),
        }
    }

    pub fn make_set(&self, raw: Vec<&str>) -> Option<HashSet<Symbol>> {
        raw.into_iter()
            .map(|name| self.solve_name(&String::from(name)))
            .collect()
    }
}
