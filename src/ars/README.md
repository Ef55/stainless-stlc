# Framework for ARS definitions

## Introduction

Ideally the best way to deal with ARS would be to define them in a very abstract and high-level manner in order to prove properties about them.
For an example of such an implementation (cf. [IdealARS](IdealARS.scala)). However, Stainless does not support some abstractions features such as bounded type operators.
Therefore, here is a framework on how to implement ARS in a consistent manner and how to reason about them.

Every ARS works on a term set $\mathcal{T}$. In the rest of the code, the class that represents $\mathcal{T}$ will be called ```T```. In general $\mathcal{T}$ will be either the terms of the calculu, but in the case of higher order calculi this can also be the set of types, kinds, ...

An ARS needs to define a reduction relation