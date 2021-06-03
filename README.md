# Model Based Projection for BV formulae

original algorithm www.cs.fsu.edu/~grigory/bvspacer.pdf


# Usage example:
```dotnet run test_formulae/test.smt x```
where test_formulae/test.smt - benchmark in smtlib format, and x - const name to eliminate.
### Output example:
```
(assert (not (= b #x00)))
(assert (not (= a #x00)))
(assert (not (bvule (bvadd #xff b) (bvadd #xff a))))
(assert (= ((_ extract 7 7) a) #b0))
Is under-approximation: True
Is trivial: False
```
