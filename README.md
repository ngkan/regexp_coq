# Regexp in coq

Started as a university project, this project attemps to define regular expression in Coq and prove related lemmas and properties.

Words and languages are defined as follow:
```
Notation word := (list A).
Notation language := (word -> Prop).
```
and being used to develop more complited terms. 

Notable lemmas

- `langKleenKleen`: Kleen closure of Kleen closure of a language is equivalent to Kleen closure of that language.
- `regular_regexp`: the language represented by a regular expression is regular.
- `regexp_regular`: any regular language can be represented by a regular expression.
- `rmatch_correct`: the Brzozowski's derivative can be used to check if a word belongs to a regular language.

Misc lemmas

- `langKleenKleen`: Kleen closure of Kleen closure of a language is equivalent to Kleen closure of that language.