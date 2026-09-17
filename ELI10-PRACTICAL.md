# ELI10: what the expanded project is trying to do

Imagine a giant Lego machine.  You cannot remember every Lego piece, so you
write down a shorter description of the machine.

Maybe your description says

```text
red light = on
blue light = off
```

The important question is not whether that description looks sensible.  The
question is:

```text
If two Lego machines get the same short description, will they behave the same
way later?
```

If yes, your short description kept enough information for that prediction.

If no, the program should show you the two machines it accidentally treated as
the same.

Then you can ask what differs between them.  Maybe one has a longer chain, one
has three steps left, or one has a bigger cluster.  Add that missing fact to the
short description and test again.

So the practical loop is

```text
make a simple state
      |
test it
      |
   does it fail?
   /          \
 no            yes
 |              |
keep it      show the two states
                |
           find what differs
                |
           add that feature
                |
              test again
```

The scanner example now does exactly this in Lean:

```text
local patterns only
    -> fail

missing fact = distance remaining
    -> add it
    -> exact prediction of the whole completion-time curve
```

Real biology will usually not be perfectly exact, so the repo also allows an
error budget.  Instead of saying two merged states must behave exactly the same,
you can ask whether their difference is at most `epsilon`.

And because the original paper proves that no perfect yes/no algorithm can work
for every possible BioNetGen model, the honest software answer has three choices:

```text
YES      I can prove the reduction works.
NO       Here are two states proving it fails.
UNKNOWN  I could not prove either one.
```

That is the expanded project's practical goal.
