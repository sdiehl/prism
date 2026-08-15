# The Prism Way

Every young language eventually announces a "way," the programming-language equivalent of arranging six ordinary rocks and calling the result a Zen garden. Prism continues the cliché, but takes it to the level of absurdity because this is a fun language, not a serious one!

There are six gates, numbered from zero because enlightenment naturally follows zero-indexing conventions as the universe intends:

0. **Shape the impossible.** If an invalid value cannot be constructed, it cannot cause a bug. If no values can be constructed, the type is perfect.
1. **The program is not the world.** Prism keeps asking which parts of reality belong in the computation and which parts should remain outside it. Enlightenment is not modelling everything. It is knowing what can be left out.
2. **State is an illusion.** Does the program mutate while the world holds still, or does the world mutate around a program that only remembers? Prefer expressions and immutable transformations. If mutation is the clearest description of the algorithm, permit it briefly, then let ownership return the object to silence.
3. **Name the world.** Effects are the labels on the doors through which reality enters. Handle a label and it leaves the outward contract. The universe has not become pure. It has merely been given a type.
4. **Detach from use.** Coeffects say how a value may be used: once, here, without escape, without allocation. The compiler checks the attachment, then invites the value to let go.
5. **Hash the emptiness.** Canonical Core gives behavior an identity, so caches, replay, diffs, and builds can ask whether a computation is still itself. The final question is whether it needed to exist at all.

> "Master, what is an effect?"
>
> "Anything that leaves the program."
>
> "Non-determinism?"
>
> "An effect."
>
> "Termination?"
>
> "An effect."
>
> "Allocation?"
>
> "An effect."
>
> "The world?"
>
> "Especially the world."
>
> "Existence?"
>
> "The first effect."
>
> The student purified the program until it had no effects left. It did not run, allocate, terminate, or exist. The compiler truncated the file to zero bytes.
>
> "Master, where did it go?"
>
> "It has achieved referential transparency."

The joke has a practical point. Real Prism programs read files, print output, allocate data, and cross named effect boundaries. Keep pure computation separate from observation, make resource promises explicit, and let the compiler erase what nobody needs. With the same code identity and recorded observations, Prism aims for the same result across the interpreter and native backends.

That is enough for a first tour. Continue with the [Language Specification](../spec.md) when you want the precise rules, browse the [Standard Library](../stdlib/index.md) for the available building blocks, and open the [Compiler](../compiler.md) chapter when phrases like "canonical Core hash" start sounding less like a metaphor and more like an implementation question.

**Further reading:** [record and replay](../spec.md#record-and-replay), [lineage](../spec.md#lineage), [source, surface, and Core identity](../compiler.md#three-identities), and [reference counting and in-place reuse](../compiler.md#reference-counting-and-fbip-reuse).
