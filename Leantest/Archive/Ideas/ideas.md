

# Ideas que he tenido pero que no se como continuar

## 1. Gn_for_each_n.lean

Idea: definir una función G_n para cada n. Si quiero tener una función G sobre los naturales que cumpla una propiedad P, y demuestro que para cada n natural existe una función G_n que cumple P, puedo tomar el límite de esa sucesión de funciones...

Problema: no necesariamente es cierto que existe tal función G cumpliendo P

Contenidos:

* lemma exists_G

    Sean
    - (X, T) un espacio topológico normal
    - C1, C2 cerrados de X disjuntos

    Entonces para cada n > 1, existe una función G_n : ℕ → P(X) de manera que cumple:
    1. ∀ p ≤ n, G_n(p) es un conjunto abierto
    2. ∀ p, q ≤ n, f p < f q → Closure(G_n(p)) ⊆ G_n(q)
    2. G_n(0) = X \ C2
    3. G_n(1) = V,, C1 ⊆ V ⊆ Closure(V) ⊆ X \ C2

* def Gn

    Def: para cada n > 1, definimos G(n) como una elección del resultado anterior
    
    Problema: esta elección no me asegura que G_n(n) = G_m(n) para n < m

* def G'

    Def: definimos G' : ℕ → P(X) como
    G'(0) = X \ C2
    G'(1) = V,, C1 ⊆ V ⊆ Closure(V) ⊆ X \ C2
    G'(n) = G_n(n)

* def G

    Def: definimos la función final que necesitamos, G : ℚ → P(X), como
    G(q) = ∅, si q < 0
    G(q) = G'(f⁻¹(q)), si 0 ≤ q ≤ 1
    G(q) = X, si q > 1

* comprobar las propiedades: la propiedad 2 no se cumple globalmente

