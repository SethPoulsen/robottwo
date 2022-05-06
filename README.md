# robottwo
Coq plugin that tranlates Coq proofs into natural language proofs. Design inspired by the [robotone](https://link.springer.com/article/10.1007/s10817-016-9377-1)
theorem prover.

This is a research prototype, not ready for production use!

# Example Output
Suppose we have the following proof in Coq that left multiplication preserves divisibility:

```coq
Lemma divide_mult_left : forall a b c : Z, (a | b) -> ((c * a)%Z | (c * b)%Z).
Proof.
intro a. intro b. intro c.
unfold divide.
intro H.
destruct H.
exists x.
rewrite H.
ring.
Qed.
```

After instrumenting this proof with our new `PreExplain` and `PostExplain` tactics and executing the proof, we obtain the following LaTeX output:

```latex
Let $a$ be an arbitrary element of $\mathbb{Z}$. \\
Let $b$ be an arbitrary element of $\mathbb{Z}$. \\
Let $c$ be an arbitrary element of $\mathbb{Z}$. \\
Now we must show that $(a | b) \rightarrow (c * a | c * b)$. \\
Which by the definition of divide means we need to show that $(\exists q \in \mathbb{Z}, b = q * a) \rightarrow \exists q \in \mathbb{Z}, c * b = q * (c * a)$. \\
Assume that $(\exists q \in \mathbb{Z}, b = q * a)$. We will refer to this assumption as $H$. \\
Now we must show that $\exists q \in \mathbb{Z}, c * b = q * (c * a)$. \\
Let $x$ be the value that makes $H$ true. \\
Choose $q$ to be $x$. \\
Now we must show that $c * b = x * (c * a)$. \\
By $H$, this is equivalent to showing $c * (x * a) = x * (c * a)$. \\
By algebraic simplification, this is clearly true. \\
```

# Important files
- `src/robottwo.mlg`: Plugin code
- `theoreies/nums.v`: Example proofs and their instrumented versions

# Running robottwo
To run the example programs, clone the repository, install the most recent Coq (tested with 8.15.1, some other versions may also work) and the development headers (required for building Coq plugins), and run

```
make
```