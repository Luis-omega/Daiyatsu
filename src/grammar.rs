use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
    usize,
};

use crate::symbols::Symbol;
use crate::{one_or_more::OneOrMore, symbols::SymbolsRegistry};

/// This module implements the core types to be
/// used to build a parser generator engine based in a BNF grammar.
///
/// We drop the names of the productions rules and terminals
/// and instead we use [usize]. The current lower bound for
/// target_pointer_width is 16, this means we can represent
/// at least 65536 different symbols, enough for most grammars.

/// A production is of the form
/// symbol1 : symbol2 symbol3 symbol4
/// We identify it's parts as :
/// ```
/// Production{name:Id(1),values:(Id(2),vec![Id(3),Id(4)])}
/// ```
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Production {
    /// The use of [IdType] in the field [Production::name] in this
    /// definition guaranties that we can't correctly assign rules
    /// to [Symbol::Eof] and [Symbol::Empty].
    name: usize,
    /// The explicit [OneOrMore] here guaranties that the
    /// productions are nullable iff it's symbols
    /// are all nullable, and not by having empty productions.
    values: OneOrMore<Symbol>,
}

impl Production {
    pub fn from_vector(
        name: usize,
        raw_name: &String,
        raw_production: Vec<Symbol>,
    ) -> Result<Self, GrammarError> {
        match OneOrMore::make_option(raw_production) {
            Some(values) => Ok(Production { name, values }),
            None => Err(GrammarError::EmptyProduction(raw_name.clone())),
        }
    }

    pub fn to_string(&self, table: &SymbolsRegistry) -> Option<String> {
        let name = table.solve_id(self.name)?;
        let productions: Vec<&str> = self
            .values
            .iter()
            .map(|symbol| table.solve_symbol(*symbol))
            .collect::<Option<Vec<_>>>()?
            .iter()
            .map(|s| s.as_str())
            .collect();
        let rendered_production = productions.join(" ");
        Some(format!("{} : {}", name, rendered_production))
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Rule {
    /// This also help us with the guaranties that a
    /// [Symbol] is nullable iff it has at least one
    /// explicit production with at least one element
    /// and all it's components are nullable.
    productions: OneOrMore<Production>,
}

impl Rule {
    pub fn from_vector(
        name: usize,
        raw_name: &String,
        raw_rule: Vec<Vec<Symbol>>,
    ) -> Result<Self, GrammarError> {
        let mut productions: Vec<Production> =
            Vec::with_capacity(raw_rule.len());
        let mut errors: Vec<GrammarError> = vec![];
        for raw_production in raw_rule {
            match Production::from_vector(name, raw_name, raw_production) {
                Ok(production) => productions.push(production),
                Err(x) => errors.push(x),
            }
        }
        match OneOrMore::make_option(productions) {
            None => {
                let last_error = GrammarError::EmptyRule(raw_name.clone());
                if errors.len() == 0 {
                    Err(last_error)
                } else {
                    errors.push(last_error);
                    Err(GrammarError::MultipleErrors(errors))
                }
            }
            Some(rule_inner) => {
                if errors.len() == 0 {
                    Ok(Rule {
                        productions: rule_inner,
                    })
                } else if errors.len() == 1 {
                    Err(errors.remove(0))
                } else {
                    Err(GrammarError::MultipleErrors(errors))
                }
            }
        }
    }

    pub fn to_string(&self, table: &SymbolsRegistry) -> Option<String> {
        let acc: Vec<String> = self
            .productions
            .iter()
            .map(|i| i.to_string(table))
            .collect::<Option<Vec<_>>>()?;
        Some(acc.join(";\n"))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Grammar {
    /// A [Symbol::Id] maps directly to element of this
    /// vector [Grammar::rules] if they are non terminals,
    /// otherwise they are terminals.
    rules: Vec<Rule>,
    len: usize,
    registry: SymbolsRegistry,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum GrammarError {
    MultipleErrors(Vec<GrammarError>),
    EmptyProduction(String),
    EmptyRule(String),
}

impl Grammar {
    #[inline]
    pub fn get_rule(&self, i: usize) -> Option<&Rule> {
        self.rules.get(i)
    }

    #[inline]
    pub fn transitive_closure<T>(
        &self,
        new: fn() -> T,
        step: fn(&mut T, &Grammar) -> bool,
    ) -> T {
        let mut arg = new();
        loop {
            if !step(&mut arg, self) {
                break;
            }
        }
        arg
    }

    pub fn from_table(
        raw_grammar: &HashMap<String, Vec<Vec<String>>>,
    ) -> Result<Grammar, GrammarError> {
        let (registry, raw_rules) = SymbolsRegistry::make(raw_grammar);
        let mut rules: Vec<Rule> = Vec::new();
        let mut errors: Vec<GrammarError> = Vec::new();
        for (name, raw_rule) in raw_rules.into_iter().enumerate() {
            match registry.solve_id(name) {
                Some(raw_name) => {
                    match Rule::from_vector(name, raw_name, raw_rule) {
                        Ok(rule) => rules.push(rule),
                        Err(e) => errors.push(e),
                    }
                }
                None => continue,
            }
        }
        if errors.len() == 0 {
            let len = rules.len();
            Ok(Grammar {
                rules,
                len,
                registry,
            })
        } else if errors.len() == 1 {
            Err(errors.remove(0))
        } else {
            Err(GrammarError::MultipleErrors(errors))
        }
    }

    pub fn from_vector(
        raw_grammar: Vec<(&str, Vec<Vec<&str>>)>,
    ) -> Result<Grammar, GrammarError> {
        let mut dic = HashMap::new();
        for (name, productions) in raw_grammar.into_iter() {
            let new_name = String::from(name);
            let mut rule = Vec::new();
            for production in productions {
                let new_production: Vec<String> = production
                    .into_iter()
                    .map(|name2: &str| String::from(name2))
                    .collect();
                rule.push(new_production);
            }
            dic.insert(new_name, rule);
        }
        Grammar::from_table(&dic)
    }

    pub fn to_string(&self) -> Option<String> {
        let acc: Vec<String> = self
            .rules
            .iter()
            .map(|i| i.to_string(&self.registry))
            .collect::<Option<Vec<_>>>()?;
        Some(acc.join("\n"))
    }
}

/// The computed First Sets for every non terminal
/// in a [Grammar], that's why [new] require
/// a [Grammar].
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FirstSets {
    sets: Vec<HashSet<Symbol>>,
}

impl FirstSets {
    pub fn new(grammar: &Grammar) -> Self {
        let grammar_len = grammar.len;
        let mut v = Vec::with_capacity(grammar_len);
        for i in 0usize..grammar_len {
            v[i] = HashSet::new();
        }
        FirstSets { sets: v }
    }
}

#[inline]
pub fn is_terminal(name: &Symbol, grammar: &Grammar) -> bool {
    match *name {
        Symbol::Id(x) => (grammar.len) <= x,
        _ => true,
    }
}

/// The returned bool is used to know if we
/// mutated the set.
pub fn compute_nullables_step(
    nullables: &mut HashSet<Symbol>,
    grammar: &Grammar,
) -> bool {
    let mut flag = false;
    for (index, rule) in grammar.rules.iter().enumerate() {
        if nullables.contains(&Symbol::Id(index)) {
            continue;
        }
        for production in rule.productions.iter() {
            let mut all_are_nullable = true;
            for item in production.values.iter() {
                if (is_terminal(item, grammar) && item.is_empty())
                    || nullables.contains(item)
                {
                    continue;
                } else {
                    all_are_nullable = false;
                    break;
                }
            }
            if all_are_nullable {
                flag = true;
                nullables.insert(Symbol::Id(production.name));
                break;
            }
        }
    }
    flag
}

/// The [Symbol::Empty] is always included.
pub fn compute_nullables(grammar: &Grammar) -> HashSet<Symbol> {
    grammar.transitive_closure(
        || HashSet::from([Symbol::Empty]),
        compute_nullables_step,
    )
}

pub fn compute_first_sets_step(
    sets: &mut Vec<Rc<RefCell<HashSet<Symbol>>>>,
    nullables: &HashSet<Symbol>,
    grammar: &Grammar,
) -> bool {
    // This tell us if we mutated [sets]
    let mut flag = false;
    for (index, rule) in grammar.rules.iter().enumerate() {
        let current_firsts = unsafe { sets.get_unchecked(index).clone() };
        for production in rule.productions.iter() {
            for item in production.values.iter() {
                let item_firsts: &HashSet<Symbol> = match *item {
                    Symbol::Id(item_id) => unsafe {
                        &(sets.get_unchecked(item_id).borrow())
                    },
                    _ => &HashSet::from([*item]),
                };
                let difference =
                    item_firsts - &(*current_firsts.clone().borrow());
                if !difference.is_empty() {
                    flag = true;
                    let mut current_firsts_mut =
                        (&*current_firsts).borrow_mut();
                    current_firsts_mut.extend(difference);
                }
                if !nullables.contains(item) {
                    break;
                }
            }
        }
        sets.insert(index, current_firsts);
    }
    flag
}

//TODO: Add tests
// - We need a function to map a ["name", ["symbol1","symbol2"]]
//      to a FirstSets
// - Modify macros and test to include
// - We change the test aproach, we are going to test all the functions
//   related to the grammars instead of by feature
pub fn compute_first_sets(
    nullables: &HashSet<Symbol>,
    grammar: &Grammar,
) -> FirstSets {
    let mut arg = Vec::with_capacity(grammar.len);
    for i in 0usize..grammar.len {
        arg[i] = Rc::new(RefCell::new(HashSet::new()));
    }
    loop {
        if !compute_first_sets_step(&mut arg, nullables, grammar) {
            break;
        }
    }
    let mut out: Vec<HashSet<Symbol>> = Vec::with_capacity(arg.capacity());
    for (index, value) in arg.into_iter().enumerate() {
        out[index] = (*value).borrow().clone()
    }
    FirstSets { sets: out }
}

pub mod test_grammars {
    use super::*;
    use std::sync::LazyLock;
    pub static EMPTY_GRAMMAR: LazyLock<(Grammar, SymbolsRegistry)> =
        LazyLock::new(|| {
            Grammar::from_vector(vec![]).expect("can't create grammar!")
        });

    pub static MATH_GRAMMAR: LazyLock<(Grammar, SymbolsRegistry)> =
        LazyLock::new(|| {
            Grammar::from_vector(vec![
                (
                    "expr",
                    vec![
                        vec!["expr", "Plus", "factor"],
                        vec!["expr", "Minus", "factor"],
                        vec!["factor"],
                    ],
                ),
                (
                    "factor",
                    vec![
                        vec!["atom", "Start", "atom"],
                        vec!["atom", "Div", "atom"],
                        vec!["atom"],
                    ],
                ),
                ("atom", vec![vec!["Nat"], vec!["LParen", "atom", "RParen"]]),
            ])
            .expect("can't create grammar!")
        });
}

#[cfg(test)]
mod tests {
    use super::*;
    use paste::paste;
    use test_grammars::*;

    macro_rules! make_nullable_test {
        ($name:tt, $raw_grammar:expr, $raw_nulls:expr)=> {
            paste! {

            #[test]
            fn [< test_nullable_ $name >](){
                let grammar = Grammar::from_vector($raw_grammar).expect("can't create grammar!");
                let expected = grammar.registry.make_set($raw_nulls).expect("can't create expected set");
                let nullables = compute_nullables(&grammar);
                assert!(
                    nullables == expected,
                    "nullables = {:?}, expected = {:?}",
                    nullables,
                    expected
                )
                }
            }
        }
    }

    macro_rules! make_nullable_test_from_static {
        ($name:tt, $static_name:tt, $raw_nulls:expr) => {
            paste! {

            #[test]
            fn [< test_nullable_ $name >](){
                let grammar = &*$static_name;
                let expected = grammar.registry.make_set($raw_nulls).expect("can't create expected set");
                let nullables = compute_nullables(&grammar);
                assert!(
                    nullables == expected,
                    "nullables = {:?}, expected = {:?}",
                    nullables,
                    expected
                )
                }
            }
        };
    }

    make_nullable_test_from_static!(
        empty_grammar,
        EMPTY_GRAMMAR,
        vec!["Empty",]
    );

    make_nullable_test!(
        single_rule,
        vec![("one_rule", vec![vec!["Empty"], vec!["none"]])],
        vec!["Empty", "one_rule"]
    );

    // sep_by1 : Uint ("," Uint)* ","?
    // TODO: Maybe add
    // sep_by1 : (Uint ",")* Uint ","?
    // to and compare both imputs
    make_nullable_test!(
        sep_by1_with_maybe,
        vec![
            (
                "sep_by1",
                vec![vec!["Uint", "maybe_separator", "maybe_comma"]]
            ),
            ("maybe_comma", vec![vec!["Comma"], vec!["Empty"]]),
            (
                "maybe_separator",
                vec![vec!["Comma", "Uint"], vec!["Empty"]]
            )
        ],
        vec!["Empty", "maybe_comma", "maybe_separator"]
    );

    make_nullable_test_from_static!(
        math_grammar_dont_have_empty,
        MATH_GRAMMAR,
        vec!["Empty"]
    );
}
