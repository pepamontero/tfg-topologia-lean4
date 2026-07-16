import VersoManual
import Docs.Referencias

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Lean Theorem Prover" =>
%%%
tag := "lean-theorem-prover"
%%%

A medida que las matemáticas se vuelven más técnicas y especializadas, verificar con rigor las demostraciones formales es una tarea cada vez más costosa. Con la motivación de facilitarla, en las últimas décadas ha surgido un interés por la verificación computacional de teoremas, dando lugar al desarrollo de sistemas como Lean, Coq o Isabelle.

Dentro de este campo, distinguimos dos tipos de sistemas de verificación formal: interactivos (ITP), que proporcionan un entorno en el que el usuario guía el proceso de la demostración paso a paso, centrándose en el aspecto de "verificación", y automáticos (ATP), que buscan completar demostraciones de manera completamente autónoma {ref "ref-avigad2024theorem"}[\[4, Sección 1\]].

En este trabajo nos centraremos en el uso de *Lean Theorem Prover*, introducido en 2013 por Leonardo de Moura desde Microsoft Research. Se trata de un verificador cuyo objetivo es reducir la distancia entre demostraciones asistidas y automatizadas, combinando un lenguaje basado en la teoría de tipos dependientes con herramientas que permiten delegar sub-problemas sencillos al sistema

Aunque aquí nos limitaremos a su uso como asistente de demostración, Lean es también un lenguaje de programación funcional completo, lo que ofrece amplias posibilidades de personalización y automatización al usuario {ref "ref-avigad2024theorem"}[\[4, Sección 1\]].

En este sistema, es posible definir objetos matemáticos, especificar propiedades sobre ellos y demostrar que dichas propiedades se cumplen. Esta tarea se ve facilitada por _Mathlib_, una extensa biblioteca de matemáticas formalizadas en Lean desarrollada de manera colaborativa por una comunidad activa y en constante crecimiento {ref "ref-mathlib"}[\[5\]].

Las demostraciones son verificadas automáticamente por el núcleo lógico de Lean, que garantiza su corrección mediante un sistema de tipos expresivo y riguroso. La fiabilidad de Lean como asistente de demostración reside precisamente en la simplicidad y robustez de este núcleo {ref "ref-bailey2024type"}[\[6\]].

En esta sección seguiremos principalmente el manual en línea _Theorem Proving in Lean 4_ {ref "ref-avigad2024theorem"}[\[4\]] que es una versión actualizada del libro _Theorem Proving in Lean_ {ref "ref-avigad2021theorem"}[\[7\]] publicado en 2021 para adaptarse a la nueva versión de Lean. A nivel teórico, no existe una gran diferencia entre los dos, por lo que ambas referencias son válidas para comprender los fundamentos que exponemos aquí.

# La teoría de tipos de Lean

La teoría de conjuntos de Zermelo-Fraenkel con el axioma de elección (ZFC) es la base fundacional elegida para formalizar la mayoría de las matemáticas que conocemos. En este marco, todos los objetos matemáticos (números, funciones, estructuras algebraicas, etc.) pueden representarse como conjuntos, construidos a partir de unos pocos axiomas básicos.

Sin embargo, este sistema carece de una estructura interna diferenciada: todo objeto matemático, como un número, una función o incluso una colección de funciones son, en última instancia, conjuntos. Para lograr una representación más clara y diferenciada de los objetos matemáticos, Lean utiliza, en su lugar, un sistema basado en tipos. Además, este enfoque nos ofrece la posibilidad de establecer una correspondencia entre programas y demostraciones matemáticas, conocida como la correspondencia de Curry-Howard{margin}[La correspondencia de Curry-Howard establece una relación entre lógica y programación; permite entender como pueden ser equivalentes "demostrar una proposición" y "construir un término de cierto tipo". Veremos qué quiere decir esto en la práctica más adelante, pero las ideas más profundas, que quedan fuera del alcance de este trabajo, se exponen detalladamente en {ref "ref-sorensen2006lectures"}[\[8\]].].

En particular, Lean se fundamenta en el _Cálculo de Construcciones Inductivas_, una extensión del cálculo de tipos dependientes que incorpora tipos inductivos y una jerarquía numerable no acumulativa de universos {ref "ref-coquand1986calculus"}[\[9\]]. Aunque no es necesario entender este sistema para utilizar Lean como asistente de demostración, a continuación daremos una breve explicación de los conceptos fundamentales: la teoría de tipos, el cálculo lambda, la incorporación de tipos a esta última, y la introducción de tipos dependientes.

En esta sección, veremos varios fragmentos de código en Lean. Lean cuenta con un compilador interactivo que procesa cada línea cuando el cursor se encuentra sobre ella, mostrando el resultado por pantalla. A partir de ahora, los comentarios que acompañan al código reflejan la salida que Lean devuelve en cada línea. Los comentarios en Lean se escriben empezando con doble guión ($`--`) y están en color gris.

## Teoría de tipos

Empecemos por lo más básico: la teoría de tipos. Cambiamos el paradigma de "cada objeto es un conjunto", propio de ZFC, a "cada objeto es un término con un tipo asociado". Esto nos permite estructurar con mayor claridad los objetos matemáticos y sus relaciones.

Por ejemplo, $`3` es un término de tipo "natural" ($`\mathbb{N}`), mientras que "true" es un término de tipo "booleano". En Lean, podemos comprobar el tipo de estas expresiones utilizando el comando `#check`.

```
#check 3    -- 3 : ℕ
#check true   -- Bool.true : Bool
```

Como en este ejemplo, en Lean utilizamos el símbolo $`:` para describir la información sobre el tipado. Es decir, si $`x` es un término de tipo $`X`, escribimos $`x : X`.

Por otro lado, un tipo, como es $`\mathbb{N}`, también es un término. Podemos comprobar su tipo:

```
#check ℕ    -- ℕ : Type
```

En Lean, los tipos tienen su propio tipo, que recibe el nombre de `Type`. Esto nos permite definir nuevos tipos. Podemos utilizar el comando `variable` para definir objetos en nuestro código{margin}[Veremos este comando en detalle más adelante.].

```
variable (X : Type)
#check X    -- X : Type
variable (x : X)
#check x    -- x : X
```

Ahora, podemos combinar distintos tipos para obtener tipos más complejos. Sean $`X` e $`Y` dos tipos. Podemos considerar el tipo $`X \times Y`, que denota los pares formados por un elemento de $`X` y otro de $`Y`. El tipo que más utilizaremos es $`X \to Y`, que denota las funciones de $`X` en $`Y`. Escribimos esto en Lean.

```
variable (X Y : Type)
#check X × Y    -- X × Y : Type
variable (x : X) (y : Y)
#check (x, y)    -- (x, y) : X × Y

#check X → Y    -- X → Y : Type
variable (f : X → Y)
#check f    -- f : X → Y
```

Por otro lado, a partir de la yuxtaposición de términos simples, podemos formar términos más complejos. En Lean, las reglas de tipado dictan el tipo de estos nuevos términos obtenidos. Por ejemplo, si $`x` es de tipo $`X` y $`f` es de tipo $`A \to B`, como en el ejemplo anterior, entonces $`f x` tiene tipo $`B`. En efecto:

```
#check f x    -- f x : Y
```

Como ocurre en el ejemplo anterior, Lean puede deducir automáticamente el tipo de muchos términos a partir del contexto. Esta capacidad se conoce como *inferencia de tipos* y en muchas ocasiones nos facilita el trabajo, permitiendo un código más conciso.

# El cálculo lambda

El Cálculo Lambda, introducido por Alonzo Church en los años 1930, es un sistema formal que permite construir expresiones mediante dos operaciones básicas: la abstracción y la aplicación {ref "ref-pierce2002types"}[\[10\]]. En este sistema, algunas expresiones representan funciones (usando la notación lambda) y otras representan valores sobre los que pueden aplicarse dichas funciones. Dos expresiones pueden yuxtaponerse para formar una nueva expresión; si la primera es una abstracción, entonces se interpreta como aplicación funcional. A partir de ahí, pueden realizarse reducciones para simplificar la expresión resultante si corresponde.

Por ejemplo, un término válido podría ser $`\lambda n, n + 2`, que representa una función que puede aplicarse a un valor para obtener otro.

En Lean, definimos funciones utilizando el comando `fun`, que corresponde a la notación $`\lambda` del cálculo lambda clásico{margin}[En la versión anterior de Lean, se utilizaba la notación `λ n, n + 2`, sin embargo en esta última versión se ha cambiado a `fun n ↦ n + 2` para mejorar la legibilidad del código.]. Por ejemplo{margin}[Estudiaremos el comando `def` en detalle más adelante.]:

```
def f := fun n ↦ n + 2
```

Además, Lean admite reducción por aplicación funcional sobre estos términos. Por ejemplo, si aplicamos la anterior función a $`3`, $`(n \mapsto n + 2)3`, se puede reducir a $`3 + 2` por aplicación funcional, y, suponiendo que la operación $`+` estaba definida anteriormente, podemos reducir esta expresión a $`5`. Podemos comprobar el resultado de esta reducción utilizando el comando `#eval`.

```
#eval f 3    -- 5
```

Diremos que dos términos que pueden reducirse de esta manera al mismo valor son *iguales por definición*. Lean trata términos que sean iguales por definición como literalmente iguales, como veremos en la práctica.

## Cálculo lambda tipado

El cálculo lambda clásico no incorpora tipos: cualquier función puede aplicarse a cualquier argumento. Para evitar inconsistencias y dar más estructura, se introduce el cálculo lambda tipado, donde a cada término se le asocia un tipo concreto.

Podemos escribir el ejemplo anterior de la siguiente forma en Lean:

```
def f : ℕ → ℕ := fun n => 2 * n
```

Aquí, estamos indicando que $`f` tiene tipo $`\mathbb{N} \to \mathbb{N}`, es decir, que es una función que toma valores en $`\mathbb{N}` y devuelve valores en $`\mathbb{N}`. Esta información permite a Lean verificar que las expresiones están bien formadas.

## Teoría de tipos dependientes

Para poder expresar los distintos objetos matemáticos en esta teoría, necesitamos introducir los tipos dependientes. Un tipo dependiente es aquel que puede variar en función de un término.

Por ejemplo, en Lean, el tipo `List α` representa una lista de elementos de tipo $`\alpha`. Si definimos un objeto de tipo `List α`, el tipo de este objeto dependerá del tipo $`\alpha` que le asignemos Internamente, se define como una función de tipo `Type u → Type u`.

```
#check List    -- List.{u} (α : Type u) : Type u
#check List ℝ    -- List ℝ : Type
```

Podemos pensar en los tipos dependientes como una generalización de las funciones que van de un tipo en otro tipo, y el tipo de llegada puede depender del tipo de entrada. Llamamos "funciones dependientes" a este tipo de funciones.

En particular, la proposición $`\forall x \in \mathbb{N}, P x` se representa en Lean mediante un tipo dependiente que expresa el conjunto de las funciones que, dado un elemento $`x \in \mathbb{N}`, devuelve una prueba de $`P x`. La notación de Lean para este tipo de construcción es `Π x : ℕ, P x`. El operador $`\Pi` sirve para denotar que el tipo de salida puede depender del valor de entrada.

## Jerarquía de universos

Puesto que en la teoría de tipos cada elemento tiene un tipo, también el tipo `Type` tiene un tipo asociado. Pero si escribiésemos simplemente `Type : Type`, el sistema caería en una inconsistencia similar a la paradoja de Russel. Para evitar esto, Lean introduce una jerarquía infinita de universos: `Type 0 : Type 1`, `Type 1 : Type 2`, y así sucesivamente.

Esta jerarquía no es acumulativa, lo que significa que si `A : Type u`, no se asume en general que `A : Type (u+1)`. Esto permite que Lean controle mejor cómo se combinan los tipos y evite ambigüedades al determinar a qué universo pertenece cada término, aunque puede realizar ciertas conversiones automáticamente cuando es seguro hacerlo. Por ello, en la mayoría de los casos no es necesario trabajar explícitamente con estos universos.

## Tipos inductivos

En Lean, la gran mayoría de tipos son instancias de una familia de tipos conocidos como *tipos inductivos*. Un tipo inductivo es una estructura formada por una lista finita de constructores, cada uno con su tipo correspondiente. Cada constructor describe una forma válida de construir un término de este nuevo tipo.

En Lean, definimos un tipo inductivo utilizando la palabra clave `inductive`{margin}[Aunque en Lean los tipos inductivos se introducen como una construcción primitiva del lenguaje, pueden definirse de manera equivalente sólo en términos de tipos dependientes. Esta reducción se explora formalmente en {ref "ref-carneiro2019type"}[\[11\]].].

```
inductive Foo where
  | constructor₁ : ... → Foo
  | constructor₂ : ... → Foo
  ...
  | constructorₙ : ... → Foo
```

Un ejemplo clásico de definición inductiva es el conjunto de los números naturales, $`\mathbb{N}`. En Lean, podemos describir el tipo `Nat` de los números naturales como

```
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
```

Internamente, la declaración `inductive` genera automáticamente una colección de axiomas que definen el tipo:

* Una constante, `Nat`, que representa el nuevo tipo.
* Una serie de reglas de introducción o constructores, que indican las posibles formas de construir términos del nuevo tipo.
* Una regla de eliminación, `Nat.rec`, que indica la forma de "usar" un término de este tipo{margin}[El comando `#print` muestra la definición completa del objeto, a diferencia de `#check`, que solo muestra su tipo.].

```
#print Nat.rec
    -- recursor Nat.rec.{u}  :  {motive : ℕ → Sort u} → motive Nat.zero → ((n : ℕ) → motive n → motive n.succ) → (t : ℕ) → motive t
```

Es decir, `inductive` puede verse como _azúcar sintáctico_ que genera automáticamente el siguiente código en Lean{margin}[Estudiaremos el comando `axiom` en detalle más adelante.]:

```
axiom (Nat : Type)
axiom (zero : Nat)
axiom (succ : Nat → Nat)
axiom (Nat.rec : {motive : Nat → Sort u} → motive Nat.zero →
  ((n : Nat) → motive n → motive Nat.succ n) → (t : Nat) →
  motive t)
```

Este último objeto, `Nat.rec`, codifica el principio de inducción sobre los naturales{margin}[`Nat.rec` es un tipo que depende de `motive`, que es una propiedad cualquiera sobre los naturales. `Nat.rec` nos dice que si se cumple `motive` para `Nat.zero` (`motive Nat.zero`), entonces si para cada `n` (`n : Nat`) que cumpla `motive` (`motive n`) se tiene que `n+1` cumple `motive` (`motive Nat.succ n`), entonces se cumple `motive` para cualquier `n` (`(t : Nat) → motive t`).]. Este principio se utiliza implícitamente en muchas definiciones por casos, como por ejemplo:

```
def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)
```

En esta definición, utilizamos la expresión `match n with` para distinguir los dos posibles casos de un número natural: `zero` y `succ n`. Internamente, Lean compila esta expresión como una aplicación de `Nat.rec`. Veremos más adelante cómo este principio de inducción puede utilizarse no solo para definir funciones, sino también para probar propiedades sobre todos los términos de un tipo inductivo.

Cabe destacar que existen otras construcciones en Lean, como `structure` o `class`, que se definen internamente como casos particulares de tipos inductivos, pero se añaden como construcciones separadas para añadir legibilidad y funcionalidad. Veremos algunos ejemplos de su uso a lo largo del trabajo.

Finalmente, mediante los tipos inductivos es posible definir los conectores lógicos (negación, conjunción, disyunción e implicación). Esto constituye otra gran diferencia entre la teoría de conjuntos y el cálculo de construcciones inductivas. Para utilizar la teoría de conjuntos, es necesario haber desarrollado previamente la lógica (de primer orden). De esta manera, las demostraciones formales no constituyen objetos matemáticos, sino que viven exclusivamente en el plano meta-teórico.

En el cálculo de construcciones inductivas, en cambio, la lógica se expresa dentro de la misma teoría, y las demostraciones son objetos matemáticos que viven dentro de ella.

## Las demostraciones como objeto matemático

Las proposiciones, como cualquier otro objeto en esta teoría, son términos con un tipo asociado. En Lean, este tipo recibe el nombre de `Prop`.

```
#check Prop    -- Prop : Type
#print True    -- inductive True : Prop
```

```
variable (P : Prop)
#check P    -- P : Prop
#check ¬ P    -- ¬ P : Prop
```

En Lean, interpretamos los objetos de tipo `Prop` como tipos en sí mismos y las demostraciones de cada proposición como términos que habitan este tipo, siguiendo la correspondencia de Curry-Howard. Es decir, una proposición `p : Prop` es el tipo de las demostraciones de `p`; una expresión de la forma `h : p` quiere decir que `h` es una demostración de `p`. Decimos que una proposición `p` es verdadera si podemos construir término de tipo `p`.

```
variable (p : Prop)
variable (h : p)
#check h    -- h : p
```

Esto, junto con la teoría de tipos dependientes, nos proporciona una forma de definir cualquier resultado matemático. Por ejemplo, "ser par" es una propiedad que depende de un número natural $`n`, por lo que podríamos describirlo mediante `es_par : ℕ → Prop`. Para cada `n` natural, obtenemos un término de tipo `Prop`.

```
def es_par : ℕ → Prop := ...
#check es_par    -- es_par : ℕ → Prop
#check es_par 3    -- es_par 3 : Prop
```

En este caso, un término de tipo `es_par n` será una prueba de que `n` es par.

Además, si `p : Prop` es una proposición, Lean reconoce cualesquiera dos elementos de tipo `p` (`h1 h2 : p`) como iguales por definición: no importa qué prueba concreta tengamos, sólo importa su existencia. Esto se conoce como "irrelevacia de las demostraciones" (_proof irrelevance_).

Esta propiedad tiene consecuencias importantes. Por un lado, evita comportamientos no deseados cuando definimos estructuras que dependen de proposiciones. Por ejemplo, si quisiéramos definir un punto del primer cuadrante en $`\mathbb{R}^2` como un par de la forma `x y : ℝ × ℝ` junto con una demostración `h : x ≥ 0 ∧ y ≥ 0`, entonces, gracias a la irrelevancia de las demostraciones, podemos identificar dos puntos que tengan las mismas coordenadas, porque las pruebas `h` y `h'` asociadas a cada uno son la misma.

Por otro lado, esta misma propiedad impide acceder al contenido de una prueba. En particular, no es posible extraer directamente el testigo de la demostración de una proposición existencial del tipo $`\exists x, P(x)`, ya que todas las demostraciones de esa proposición se consideran iguales. Dada una demostración de $`\exists x, P(x)`, contamos varios métodos para obtener un testigo, uno de los cuales es usar el axioma de elección. Volveremos sobre esta cuestión más adelante.

Una última característica destacable de las proposiciones en Lean es que la implicación lógica se representa directamente mediante funciones: dadas dos proposiciones `p q : Prop`, una prueba de `p → q` es simplemente una función que, dada una prueba de `p`, devuelve una prueba de `q`. Esta identificación entre funciones e implicaciones es otra manifestación de la correspondencia de Curry-Howard.

En resumen, para poder expresar un resultado matemático en este lenguaje, tenemos que escribir un término de la forma `p : Prop`. Para probar que el resultado es cierto, debemos construir un término `h : p`. El trabajo de Lean como asistente de demostración es verificar que el término `h` está bien construido y tiene el tipo correcto.

# ¿Por qué fiarnos de Lean?

Ahora que hemos descrito la manera en la que un resultado se considera demostrado en Lean, tiene sentido hacerse la pregunta: ¿por qué deberíamos fiarnos de la inferencia de tipos de Lean? ¿Qué garantías tenemos de que las demostraciones que Lean acepta, son realmente correctas?

Como hemos señalado, demostrar un resultado en Lean consiste en construir correctamente un término que tiene un determinado tipo. Este proceso es análogo al de verificar programas: se trata de comprobar que un término está bien formado (siguiendo unas reglas concretas) y satisface una especificación dada, expresada como un tipo. Esta tarea recae sobre el núcleo (o _kernel_) de Lean, un pequeño programa que contiene la implementación mínima de la lógica interna de Lean.

El resto de componentes de Lean con el que interactuamos para construir demostraciones (como por ejemplo las tácticas que veremos después) devuelven construcciones expresadas en el lenguaje del kernel de Lean {ref "ref-bailey2024type"}[\[6\]]. Esto quiere decir que confiar en Lean realmente se reduce a confiar en su kernel{margin}[Esta idea se conoce como _criterio de de Bruijn_, que propone que un verificador formal debe producir sus pruebas en el lenguaje de un núcleo pequeño, incluso aunque utilicen otros métodos más complicados para construir dichas pruebas a priori {ref "ref-bailey2024type"}[\[6\]].].

Ahora, ¿por qué nos fiamos del kernel de Lean? Gracias a que el kernel es pequeño y está aislado del resto del sistema, es posible escribir implementaciones independientes del mismo que verifiquen de manera autónoma las demostraciones aceptadas por Lean. Lean permite exportar estas demostraciones en un formato intermedio que contiene toda la información necesaria para reconstruirlas y validarlas externamente. Además, puesto que este formato modular, es posible validar solo ciertos aspectos concretos del kernel {ref "ref-bailey2024type"}[\[6\]]. Por ejemplo, en {ref "ref-carneiro2024lean4lean"}[\[12\]], Carneiro describe una nueva implementación externa del verificador de tipos de Lean 4, escrita en el propio lenguaje Lean y capaz de verificar toda la biblioteca de Mathlib.

# Demostraciones en Lean

Hasta ahora, hemos explorado la teoría de tipos dependientes sobre la que se construye Lean, así como los fundamentos que garantizan la corrección de sus demostraciones. Pasamos por tanto a un enfoque más práctico: ¿cómo escribimos matemáticas en Lean?

Recordemos que formalizar un resultado en Lean no consiste solo en escribir su enunciado, sino también en construir una demostración paso a paso, sin omisiones y con total precisión. Aquí, nunca nos basta con escribir "trivial" cuando creamos que algo ya deberíamos poder saberlo: necesitamos convencer al sistema de que cada paso es válido.

Esta sección está dedicada a aprender a escribir demostraciones en Lean. Veremos cómo introducir nuevos objetos en nuestro contexto, cómo enunciar proposiciones y cómo construir demostraciones interactuando con Lean. También presentaremos algunas herramientas de automatización y métodos para poder apoyarnos en la librería de Mathlib.

## Axiomas, definiciones y variables

Antes de escribir demostraciones en cualquier sistema formal, necesitamos describir el *contexto* en el que trabajamos: el conjunto de objetos e hipótesis disponibles en un momento dado. Este contexto es dinámico y se va ampliando a medida que introducimos nuevos elementos.

En Lean ocurre lo mismo. El sistema mantiene y actualiza este contexto constantemente para comprobar que cada expresión está bien formada y tiene el tipo esperado.

Podemos introducir nueva información en el contexto de distintas formas. Distinguimos entre axiomas, definiciones y variables, cada una con una función lógica distinta en el sistema.

* *Axiomas*{margin}[En Lean 3, a este tipo de declaraciones se les llamaba _constantes_ y utilizaban el comando `constant`.]

Permiten introducir hipótesis que se asumen sin demostración. En particular, escribir que x "es de tipo X" es también una hipótesis, por lo que los axiomas pueden utilizarse para introducir nuevos objetos{margin}[En este sentido decíamos que definir un tipo inductivo es análogo a escribir una colección de axiomas. `inductive Nat` se puede ver como una versión estructurada de `axiom Nat : Type`, `axiom zero : Nat`, `axiom succ : Nat to Nat`, etc.]. Por ejemplo:

```
axiom P : Prop
axiom h : P → P
```

Estamos declarando una proposición $`P` y una prueba de que $`P` implica $`P`.

```
axiom n : ℕ
axiom hn : n > 2
```

Aquí estamos suponiendo que $`n` es un número natural mayor que $`2`.

Así, los axiomas nos permiten fijar hechos que queremos asumir como válidos a lo largo de nuestras demostraciones.

* *Definiciones*

Introducen objetos nuevos a partir de otros ya conocidos. A diferencia de los axiomas, no basta con indicar el tipo del nuevo objeto, sino que también hay que dar su construcción. Por ejemplo:

```
def f : ℕ → ℕ := fun n ↦ 2 * n
def n : ℕ := 3
def es_par : ℕ → Prop := fun n ↦ ∃ m, n = f m
```

Además, cuando el tipo puede inferirse a partir de la construcción, no es necesario indicarlo explícitamente:

```
def n := 3
#check n    -- n : ℕ
```

* *Variables*

En la mayoría de lenguajes de programación, estamos acostumbrados a que definir una variable implique asignarle un valor concreto. Sin embargo, en Lean las variables se comportan más bien como en lógica. Al introducir una variable $`x`, lo que se introduce es un contexto universal: siempre que $`x` aparezca de forma libre, Lean interpretará que lo que sigue está cuantificado universalmente respecto a $`x`. Por ejemplo{margin}[Las variables, a diferencia de los axiomas y las definiciones, se escriben entre paréntesis. Lo mismo ocurre con los argumentos que toman las proposiciones, como veremos más adelante. Esto está relacionado con la correspondencia de Curry–Howard: declarar una variable equivale a abstraer sobre ella, lo que corresponde a cuantificar universalmente.]:

```
variable (x : ℕ)
axiom hx : x ≥ 0
#print hx    -- axiom hx : ∀ (x : ℕ), x ≥ 0
```

## Proposiciones

Además de introducir objetos, también queremos enunciar y demostrar proposiciones. En Lean, esto se hace del mismo modo que en otros sistemas formales: primero escribimos los resultados (como lemas o teoremas) formalmente, y después proporcionamos una demostración.

Como ya hemos visto, una proposición en Lean es un término de tipo `Prop`, y una demostración de `p : Prop` es simplemente un término de tipo `p`. Por tanto, demostrar una proposición no es diferente de definir un objeto; podemos utilizar `def` para escribir resultados matemáticos. Por ejemplo:

```
def mi_prop : 1 > 0 := ...
```

Aquí estamos diciendo que `mi_prop` es un objeto de tipo `1 > 0`. Si en el lugar de `...` proporcionamos un término de tipo `1 > 0`, habremos demostrado `mi_prop`.

Sin embargo, para mayor claridad y estructura, Lean proporciona los comandos `lemma` y `theorem`. Ambos funcionan exactamente igual que `def` y son intercambiables entre sí, pero facilitan la lectura del código indicando qué objetos son resultados matemáticos, y la jerarquía de importancia entre ellos. La sintaxis es la misma:

```
lemma my_lemma : 1 > 0 := ...
theorem commutative_sum (a b : ℕ) : a + b = b + a := ...
```

Existe también el comando `example`, que sirve para escribir demostraciones sin la necesidad de nombrar el resultado:

```
example (a b : ℕ) : a * b = b * a := ...
```

Este tipo de expresiones no amplían el contexto ni definen nuevos objetos; son simplemente comprobaciones locales. Pero veremos que nos pueden ser útiles en ciertas ocasiones.

## Demostraciones: el modo táctico

Llegamos a la parte central de esta sección: *escribir demostraciones* en Lean. En general, hay dos formas de construir una demostración en Lean:

* Mediante *términos*, es decir, escribiendo directamente una expresión del tipo deseado.
* Mediante el *modo táctico*, en el que una demostración se construye paso a paso usando instrucciones llamadas *tácticas*.

En este trabajo utilizaremos exclusivamente el modo táctico, ya que es el enfoque más práctico y más cercano a la forma en que razonamos al escribir demostraciones matemáticas en lenguaje natural.

En una demostración informal, solemos avanzar mediante pasos lógicos encadenados: "supongamos que...", "entonces...", "por el lema..., se tiene...". Cada uno de estos pasos se traduce en Lean mediante una táctica: una instrucción que modifica el estado de la demostración, ya sea introduciendo hipótesis, aplicando resultados conocidos, dividiendo el objetivo en partes más manejables, etc.

Además, el modo táctico nos permite trabajar de manera *interactiva* con Lean. Si escribimos un enunciado, e inmediatamente después de `:=` escribimos `by`, estamos indicando a Lean que para la construcción de este término vamos a utilizar el modo táctico. Por ejemplo:

```
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
```

Estamos indicando que queremos construir un término de tipo `p ∧ q` a partir de las hipótesis `hp : p` y `hq : q`, y que para esa construcción vamos a utilizar el modo táctico.

Internamente, Lean interpreta esto mediante la generación de un contexto local (nuestras hipótesis) y un *objetivo* (nuestra tesis), que consiste en construir el término del tipo esperado. Después de `by`, podemos empezar a escribir tácticas, que Lean interpretará actualizando el contexto y el objetivos.

Este objetivo aparece reflejado en el *InfoView*, una ventana que muestra el estado actual de nuestra demostración. Lean procesa línea a línea de forma automática, por lo que en cualquier momento podemos consultar el impacto de haber aplicado una táctica simplemente colocando el cursor sobre la línea de código correspondiente.

De hecho, en el InfoView también se muestran los resultados de las instrucciones que ya hemos visto como `#check`, `#print` o `#eval`.

![Captura del InfoView de Lean mostrando el resultado de comprobar el tipo de una expresión con el comando #check.](figuras/check-example-light-version.png)

En general, mientras escribimos en Lean, tendremos abierta esta ventana paralelamente a nuestro código, para poder ir viendo el progreso de nuestra demostración.

![Captura del InfoView de Lean mostrando el estado táctico (Tactic state) de una demostración, con el contexto de hipótesis y el objetivo marcado con el símbolo ⊢.](figuras/theorem-example-light-version.png)

Bajo el apartado `Tactic state`, podemos comprobar:

* El número de tesis que nos quedan por demostrar (en este caso solo una: `1 goal`).
* Nuestro contexto.
* La (o las) tesis, marcada con el símbolo `⊢`.

A partir de este punto, podemos empezar a añadir las tácticas que van a constituir nuestra demostración. Las tácticas se escriben una detrás de otra, separadas por punto y coma (`;`) o por saltos de línea.

Al escribir una táctica, el apartado `Tactic state` del InfoView se actualizará según corresponda. Cuando todas las tesis se hayan resuelto, el InfoView mostrará `No goals`.

![Captura del InfoView de Lean mostrando el mensaje No goals al haberse completado la demostración.](figuras/no-goals-example-light-version.png)

## Algunas tácticas básicas

En esta sección veremos algunas de las tácticas más básicas y útiles para construir demostraciones en Lean. Veremos cómo se aplican y qué efecto tienen en el InfoView. El resto de tácticas que aparecen a lo largo del trabajo pueden consultarse en el apartado de tácticas de la documentación de Lean, {ref "ref-tacticas"}[\[13\]].

Para poder utilizar las tácticas mencionadas a continuación, es necesario importar el módulo de Mathlib correspondiente al modo táctico mediante

```
import Mathlib.Tactic
```

A partir de aquí, en lugar de mostrar capturas del InfoView, utilizaremos dos bloques de código en paralelo: el de la izquierda contiene el código de Lean; el de la derecha representa el estado que se mostraría en el InfoView si colocásemos el cursor en la última línea.

### `intro`

La táctica `intro` introduce un nuevo objeto en el contexto, de manera similar a escribir "Supongamos que..." o "Sea..." en una demostración informal.

Es útil cuando el objetivo tiene la forma de una implicación o un cuantificador universal: transformamos la primera parte de la tesis en una nueva hipótesis y la segunda en la nueva tesis. Por ejemplo, para la implicación:

```
example (p : Prop) : p → p := by
```

_Estado en el InfoView:_

```
Tactic state
  1 goal
  p : Prop
  ⊢ p → p
```

↓

```
example (p : Prop) : p → p := by
  intro hp
```

_Estado en el InfoView:_

```
Tactic state
  1 goal
  p : Prop
  hp : p
  ⊢ p
```

Y para deshacer cuantificadores:

```
example : ∀ (p : Prop), p → p := by
```

_Estado en el InfoView:_

```
Tactic state
  1 goal
  ⊢ ∀ (p : Prop), p → p
```

↓

```
example : ∀ (p : Prop), p → p := by
  intro q
```

_Estado en el InfoView:_

```
Tactic state
  1 goal
  q : Prop
  ⊢ q → q
```

### `exact`

La táctica `exact` se utiliza cuando ya tenemos, en nuestro contexto, exactamente lo que queremos demostrar. Es decir, existe una hipótesis que coincide con la tesis actual. Por ejemplo:

```
example : ∀ (p : Prop), p → p := by
  intro p hp
```

_Estado en el InfoView:_

```
Tactic state
  1 goal
  p : Prop
  hp : p
  ⊢ p
```

↓

```
example : ∀ (p : Prop), p → p := by
  intro p hp
  exact hp
```

_Estado en el InfoView:_

```
Tactic state
  No goals
```

A modo de comparación, podríamos construir esta demostración utilizando sólo términos de la siguiente forma:

```
example : ∀ (p : Prop), p → p := fun p ↦ (fun hp : p ↦ hp)
```

En este caso puede resultar más sencillo, pero en demostraciones más complejas perdemos legibilidad.

### `apply`

La táctica `apply` nos permite usar una implicación para reducir un objetivo a otro más simple. Equivale a utilizar la regla del _Modus Ponens_: si tenemos una hipótesis de la forma $`p \rightarrow q` y queremos demostrar $`q`, basta con demostrar $`p`.

```
example : (p q : Prop) (hp : p)
    (hpq : p → q) : q := by
```

_Estado en el InfoView:_

```
Tactic state
  1 goal
  p q : Prop
  hp : p
  hpq : p → q
  ⊢ q
```

↓

```
example : (p q : Prop) (hp : p)
    (hpq : p → q) : q := by
  apply hpq
```

_Estado en el InfoView:_

```
Tactic state
  1 goal
  p q : Prop
  hp : p
  hpq : p → q
  ⊢ p
```

Podríamos completar esta demostración usando `exact hp`.

### `use`

Utilizamos `use` para trabajar con el cuantificador existencial. Si queremos demostrar una proposición de la forma "$`\exists x, P x`", basta con encontrar un $`x_0` concreto que satisfaga la propiedad $`P`.

En este caso, aplicamos `use` para indicarle a Lean el valor concreto $`x_0` que queremos usar para demostrar la existencia. El objetivo pasa a ser entonces demostrar que $`x_0` satisface $`P`. Por ejemplo:

```
example : ∃ n : ℕ, n > 3 := by
```

_Estado en el InfoView:_

```
Tactic state
  1 goal
  ⊢ ∃ n, n > 3
```

↓

```
example : ∃ n : ℕ, n > 3 := by
  use 5
```

_Estado en el InfoView:_

```
Tactic state
  1 goal
  ⊢ 5 > 3
```

### `left`, `right`

Las tácticas `left` y `right` se utilizan para trabajar con disyunciones, es decir, proposiciones de la forma $`A \lor B`.

En una demostración informal, si queremos demostrar que "$`A` o $`B`" es cierto, nos basta con demostrar una de las dos. Utilizamos `left` para indicar que vamos a demostrar la parte izquierda ($`A`), y `right` si queremos demostrar la parte derecha ($`B`). Por ejemplo:

```
example : (p q : Prop) (hp : p) :
    p ∨ q := by
```

_Estado en el InfoView:_

```
Tactic state
  1 goal
  p q : Prop
  hp : p
  ⊢ p ∨ q
```

↓

```
example : (p q : Prop) (hp : p) :
    p ∨ q := by
  left
```

_Estado en el InfoView:_

```
Tactic state
  1 goal
  p q : Prop
  hp : p
  ⊢ p
```

Podríamos completar esta demostración aplicando `exact hp`.

### `constructor`

Utilizamos `constructor` para trabajar con conjunciones, es decir, proposiciones de la forma $`A \land B`.

Cuando queremos demostrar que "$`A` y $`B`" es cierto, podemos demostrar $`A` por un lado y $`B` por otro. Al aplicar `constructor`, Lean divide un objetivo `A ∧ B` en dos sub-objetivos con el mismo contexto: uno para `A` y otro para `B`. Por ejemplo:

```
example (p q : Prop) (hp : p)
    (hq : q) : p ∧ q := by
```

_Estado en el InfoView:_

```
Tactic state
  1 goal
  p q : Prop
  hp : p
  hq : q
  ⊢ p ∧ q
```

↓

```
example (p q : Prop) (hp : p)
    (hq : q) : p ∧ q := by
  constructor
```

_Estado en el InfoView:_

```
Tactic state
  2 goals
  case left
    p q : Prop
    hp : p
    hq : q
    ⊢ p
  case right
    p q : Prop
    hp : p
    hq : q
    ⊢ q
```

Después de aplicar `constructor`, el InfoView mostrará dos objetivos pendientes (`2 goals`). Al resolver cada uno por separado, completamos la demostración.

```
example (p q : Prop) (hp : p)
    (hq : q) : p ∧ q := by
  constructor
  exact hp
  exact hq
```

_Estado en el InfoView:_

```
Tactic state
  No goals
```

Aunque lo anterior es correcto, lo habitual cuando trabajamos con más de una tesis es utilizar `·` para separarlas. Cuando escribimos `·` tras un salto de línea, Lean enfoca el primer objetivo, ocultando temporalmente el resto. Por ejemplo:

```
example (p q : Prop) (hp : p)
    (hq : q) : p ∧ q := by
  constructor
  ·
```

_Estado en el InfoView:_

```
Tactic state
  1 goal
  case left
    p q : Prop
    hp : p
    hq : q
    ⊢ p
```

Si colocamos el cursor al final, el InfoView solo muestra `1 goal`, porque el segundo objetivo está oculto por ahora. La demostración completa en este estilo sería:

```
example (p q : Prop) (hp : p)
    (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq
```

_Estado en el InfoView:_

```
Tactic state
  No goals
```

### `cases'`

La táctica `cases'` se utiliza para analizar una disyunción en el contexto, es decir, una hipótesis de la forma $`A \lor B`.

En una demostración informal, equivale a hacer un razonamiento por casos: "Supongamos que ocurre $`A`, veamos si se sigue la tesis; supongamos depués que ocurre $`B`, y comprobemos si también se sigue".

Al aplicar `cases' h` sobre una hipótesis h, Lean duplica el objetivo (que no cambia), pero modifica el contexto en cada uno de los nuevos objetivos, introduciendo las hipótesis correspondientes a cada caso. Utilizamos el comando `with` para asignar nombres a las nuevas hipótesis. Por ejemplo:

```
example (p q : Prop) (h : p ∨ q)
    (hpq : p → q) : q := by
```

_Estado en el InfoView:_

```
Tactic state
  1 goal
  p q : Prop
  h : p ∨ q
  hpq : p → q
  ⊢ q
```

↓

```
example (p q : Prop) (h : p ∨ q)
    (hpq : p → q) : q := by
  cases' h with hp hq
```

_Estado en el InfoView:_

```
Tactic state
  2 goals
  case inl
    p q : Prop
    hpq : p → q
    hp : p
    ⊢ q
  case inr
    p q : Prop
    hpq : p → q
    hq : q
    ⊢ q
```

Podemos entonces completar la demostración con las herramientas que tenemos hasta ahora:

```
example (p q : Prop) (h : p ∨ q)
    (hpq : p → q) : q := by
  cases' h with hp hq
  · apply hpq
    exact hp
  · exact hq
```

_Estado en el InfoView:_

```
Tactic state
  No goals
```

Como hemos visto por medio de estos ejemplos, completar una demostración en modo táctico consiste en combinar estas instrucciones una después de otra, haciendo que las hipótesis y las tesis vayan avanzando hasta alcanzar el estado deseado: `No goals`. Las tácticas nos dan la flexibilidad necesaria para formalizar una gran variedad de resultados matemáticos.

## Herramientas de automatización y búsqueda en Mathlib

A medida que las demostraciones en Lean se vuelven más complejas, no siempre resulta práctico construir cada paso manualmente. Para agilizar el proceso, Lean incorpora algunas herramientas de automatización que permiten delegar ciertas tareas al sistema.

Además, en lugar de volver a demostrar resultados que ya están formalizados, es fundamental *aprovechar la biblioteca matemática de Lean, Mathlib*, que contiene miles de definiciones y teoremas disponibles para su reutilización.

Sin embargo, apoyarse en Mathlib no siempre es directo: los resultados pueden tener nombres poco intuitivos o muy específicos, y encontrar el lema que necesitamos en un momento dado no es siempre fácil.

Por ejemplo, un resultado tan simple como: "Si $`a, b, c` son números reales tales que $`a < b` y $`c < 0`, entonces $`a + c < b`" (que en una prueba informal consideraríamos casi trivial), aparece en Mathlib con el nombre `add_lt_of_lt_of_neg'`. En la práctica, recordar todos estos nombres resulta inviable, incluso para resultados elementales.

En esta sección introduciremos las tácticas `simp` y `exact?`, que nos ayudan a resolver objetivos simples, y dos herramientas externas que podemos utilizar para localizar resultados en Mathlib. Además, veremos la forma en la que integrar estas herramientas en nuestro proceso de demostración de resultados.

### `simp`

La manera más sencilla de apoyarse en la librería de Mathlib es utilizar la táctica `simp`. Esta táctica hace una búsqueda exhaustiva entre una base de datos de lemas de Mathlib que están marcados con el atributo `simp`, intentando simplificar lo máximo posible el objetivo o las hipótesis a las que se aplique.

La táctica `simp` se puede utilizar en cualquier momento de la demostración, pero resulta especialmente útil cuando algo que queremos demostrar parece evidente o suficientemente simple. Por ejemplo:

```
example (G : Type) [Group G] (a b c : G) :
    a * a⁻¹ * 1 * b = b * c * c⁻¹ := by
  simp
```

Solamente usando `simp` podemos terminar la demostración en este caso. Realmente, lo único que hace es reescribir reiteradamente resultados de la forma `A = B` ó `A ↔ B`, hasta que no puede reescribir nada más, de manera mecánica. Por tanto, aunque es útil en muchos casos, en otros es posible que no nos ayude.

En la práctica, cuando nos resulte sencillo utilizar otras tácticas o resultados conocidos, eso será preferible a utilizar `simp`, primero porque al tratarse de una búsqueda exhaustiva, no es una táctica computacionalmente eficiente, y segundo porque empeora la legibilidad del código, ya que a veces es difícil saber cómo ocurren ciertas simplificaciones.

### `exact?`

Lean incorpora algunas tácticas que intentan cerrar el objetivo actual utilizando tanto las hipótesis del contexto como los resultados disponibles en los archivos importados. Las más destacadas son `exact?`{margin}[La táctica `exact?` tenía el nombre `library_search` en Lean 3.] y `apply?`.

A lo largo del proyecto, la que he utilizado con mayor frecuencia es `exact?`. Esta táctica intenta encontrar una expresión que tenga exactamente el tipo del objetivo actual, buscando tanto en la información local (hipótesis del contexto, resultados definidos anteriormente) como en la librería de Mathlib.

Por ejemplo, en el caso de encontrar hipótesis locales:

```
example (p : Prop) : p → p := by
  intro hp
  exact?
```

_Estado en el InfoView:_

```
Suggestions
  Try this: exact hp
```

Y en el caso de encontrar resultados de Mathlib:

```
example (n : ℕ) : n ≥ 0 := by
  exact?
```

_Estado en el InfoView:_

```
Suggestions
  Try this: exact Nat.zero_le n
```

En general, utilizar la expresión sugerida por `exact?` concluirá la prueba.

A pesar de que `exact?` nos puede ayudar en muchos casos, es una herramienta relativamente sencilla, que solo puede dar un paso (aplicar un teorema o una hipótesis). Esto implica que si no tenemos las hipótesis exactas de los teoremas como aparecen en Mathlib, `exact?` no encontrará ninguna solución.

Cuando trabajamos con hipótesis más complejas, lo habitual no es utilizar `exact?` directamente para probar nuestra tesis, sino para probar ciertos resultados intermedios. Por esto, una táctica crucial a la hora de trabajar con `exact?` es `have`, el equivalente en demostraciones informales a declarar un lema en mitad de una demostración. Por ejemplo, supongamos que queremos probar:

```
example (p q r : Prop) (hpq : p → q) (hqr : q → r) (hp : p) : r
```

En lugar de tratar de demostrar inmediatamente `r`, podríamos probar, de manera intermedia, que se tiene `q`. Para esto utilizamos `have`:

```
example (p q r : Prop) (hpq : p → q)
    (hqr : q → r) (hp : p) : r := by
  have hq : q
```

_Estado en el InfoView:_

```
Tactic state
  2 goals
  case hq
    (...)
    ⊢ q
  (...)
  ⊢ r
```

Escribir `have hq : q` introduce una nueva tesis, `q`, independiente de la anterior. Una vez completemos la prueba de esta nueva tesis, podremos usar el resultado en nuestra demostración. Por tanto, podríamos completar el ejemplo anterior de la siguiente forma:

```
example (p q r : Prop) (hpq : p → q) (hqr : q → r) (hp : p) : r := by
  have hq : q
  · apply hpq
    exact hp
  apply hqr
  exact hq
```

Recordemos que utilizamos el punto `·` para separar la demostración de `hq` del resto de la demostración.

Veamos por tanto como es el proceso de trabajar con `exact?`. Consideremos el siguiente ejemplo, para el que `exact?` no encuentra ningún resultado:

```
example (x : ℝ) (hx : x > 0) :
    x / x = 1 := by
  exact?
```

_Estado en el InfoView:_

```
Tactic state
  1 goal
  x : ℝ
  hx : x > 0
  ⊢ x / x = 1
Messages
  `exact?` could not close the goal.
```

1. Mirando el estado actual de la demostración, identificar cuál sería una hipótesis que desearíamos tener en nuestro contexto. En este caso, al tratarse de una división, podría ser necesario tener la hipótesis $`x \neq 0`.
1. Añadir la nueva tesis utilizando `have`{margin}[En algunos casos, será más útil escribir aquello que creemos poder necesitar fuera de la demostración, utilizando `example`, porque podremos escribir resultados más generales.].

  ```
  example (x : ℝ) (hx : x > 0) :
      x / x = 1 := by
    have h : x ≠ 0
    ·
  ```
  _Estado en el InfoView:_
  ```
  Tactic state
    1 goal
    x : ℝ
    hx : x > 0
    ⊢ x ≠ 0
  ```
1. Intentar demostrar la nueva tesis utilizando `exact?`.

  ```
  example (x : ℝ) (hx : x > 0) :
      x / x = 1 := by
    have h : x ≠ 0
    · exact?
  ```
  _Estado en el InfoView:_
  ```
  Suggestions
    Try this: Ne.symm (ne_of_lt hx)
  ```

Con esta nueva hipótesis, parece probable que `exact?` sea capaz de terminar la demostración. En efecto:

```
example (x : ℝ) (hx : x > 0) :
    x / x = 1 := by
  have h : x ≠ 0
  · exact Ne.symm (ne_of_lt hx)
  exact?
```

_Estado en el InfoView:_

```
Suggestions
  Try this: (div_eq_one_iff_eq h).mpr rfl
```

La táctica `exact?` es un ejemplo de motor de búsqueda formal: una herramienta que, mediante meta-programación en Lean, compara el objetivo actual con los tipos de todos los lemas disponibles y devuelve aquellos con coincidencias exactas. Por tanto, la clave de usar `exact?` de manera eficaz reside en *desarrollar gradualmente una cierta intuición* sobre qué resultados es probable que estén formalizados en Mathlib, y la forma concreta en la que están formulados.

En efecto, reconocer que un lema de Mathlib sobre división por $`x` probablemente requería la hipótesis $`x\neq0` (y no simplemente $`x>0`) ha sido esencial para poder aplicar `exact?` con éxito en el ejemplo anterior.

A parte de `exact?`, existen tácticas similares como `apply?` y `rw?`, que funcionan del mismo modo y permiten dar pasos intermedios. Sin embargo, en la práctica estas tácticas suelen devolver una larga lista de opciones, muchas de las cuales no son relevantes o útiles. Por tanto, cuando `exact?` no es suficiente, es más eficaz recurrir a otras herramientas de búsqueda.

### Otras herramientas

A lo largo de este proyecto he utilizado fundamentalmente dos herramientas externas de búsqueda en Mathlib: Moogle {ref "ref-moogle"}[\[14\]] y LeanSearch {ref "ref-gao2024semantic"}[\[15\]]. Ambos son motores de búsqueda semántica, lo que significa que no se limitan a buscar coincidencias literales en el texto, sino que intentan interpretar el significado matemático de nuestra consulta y compararlo con los resultados de Mathlib. Para ello utilizan modelos de lenguaje de gran escala (LLMs), que permiten establecer relaciones entre enunciados aunque estén formulados de distinta manera. En particular, admiten consultas con los siguientes formatos {ref "ref-gao2024semantic"}[\[15\]]:

* Descripciones en lenguaje natural
* Nombres de teoremas conocidos
* Notación matemática (en LaTeX)
* Código Lean

Por ejemplo, si en el caso anterior no se nos hubiera ocurrido la idea de demostrar primero $`x \neq 0`, podríamos haber buscado en Moogle algo del estilo de _"division by itself is 1"_. De hecho, el segundo resultado de esta búsqueda en Moogle es:

![Captura de un resultado de búsqueda en Moogle para la consulta "division by itself is 1".](figuras/moogle-example.png)

Que no es el mismo resultado que proponía `exact?`, pero parece incluso más simple. Podríamos volver a nuestro ejemplo y escribir

```
example (x : ℝ) (hx : x > 0) :
    x / x = 1 := by
  apply div_self
```

_Estado en el InfoView:_

```
Tactic state
  1 goal
  x : ℝ
  hx : x > 0
  ⊢ x ≠ 0
```

Con lo que ya sólo faltaría demostrar que $`x \neq 0`.

En general, he encontrado que LeanSearch funciona mejor que Moogle, especialmente en términos de relevancia de los resultados obtenidos. Sin embargo, al principio del proyecto solo conocía Moogle, y descubrí LeanSearch más tarde, por lo que he utilizado Moogle mayoritariamente.

Un ejemplo de una búsqueda real que necesité para el trabajo en LeanSearch, fue _"subset of set has at most the dimension of the set"_.

![Captura de un resultado de búsqueda en LeanSearch para la consulta "subset of set has at most the dimension of the set".](figuras/leansearch-example-cropped.png)

El primer resultado que aparece es justo el que necesitaba. Sin embargo, antes de buscarlo no tenía ninguna idea de cómo formalizar los resultados en los que estaba trabajando, especialmente porque no estaba familiarizada con el módulo `Cardinal`. Este fue un ejemplo claro de que estas herramientas permiten acceder a partes de Mathlib que de otro modo serían difíciles de localizar.

En conjunto, herramientas como `exact?`, LeanSearch o Moogle han resultado fundamentales para hacer más eficiente el proceso de formalización, permitiendo apoyarse en Mathlib de forma efectiva sin necesidad de conocerla en profundidad desde el principio.

## Noncomputable y el axioma de elección

Para finalizar esta sección sobre Lean en la práctica, es útil comentar brevemente una cuestión que aparecerá en algunas de las definiciones posteriores: el uso del *axioma de elección* y la palabra clave `noncomputable`.

En Lean, el axioma de elección se introduce de la siguiente forma:

```
axiom choice {α : Sort u} : Nonempty α → α
```

Es decir, dado un tipo no vacío, `choice` devuelve un elemento de ese tipo, aunque no nos dice cómo encontrarlo. Por este motivo, su uso impide extraer información computable del resultado.

En consecuencia, cuando definimos funciones o construcciones que dependen de `choice`, Lean nos obliga a marcarlas como `noncomputable`. Un ejemplo es la función `choose`, que dada una prueba de tipo existencial, selecciona un testigo:

```
noncomputable def choose {α : Sort u} {p : α → Prop}
    (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val
```

A menudo utilizaremos `choose` (`Classical.choose`, ya que se encuentra en el módulo `Classical`) en nuestros resultados, junto con el siguiente lema

```
theorem choose_spec {α : Sort u} {p : α → Prop}
    (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription p h).property
```

que es una demostración de que el elemento elegido mediante `choose` cumple las propiedades que le pedíamos.

El uso de `noncomputable` no representa un problema para nosotros (ni, en general, para la comunidad matemática), ya que en este trabajo no nos interesa que las construcciones sean computables: trabajamos con ellas desde un punto de vista lógico y matemático, no algorítmico.

Además, usar el axioma de elección tiene una ventaja práctica: cuando utilicemos `choose`, el elemento elegido será siempre el mismo (aunque no sepamos cuál es), y tendrá siempre la propiedad `choose_spec`. Esto permite trabajar con él de forma coherente dentro de una demostración y referirse a él varias veces como si fuera un objeto determinado.

En contraposición, otra forma de obtener un testigo de una prueba de existencia es utilizar la táctica `obtain`, que se utiliza de la siguiente manera:

```
example : (∃ n : ℕ, n > 3) → ∃ m : ℕ, m > 2 := by
intro h   -- h : ∃ n : ℕ, n > 3
obtain ⟨n, hn⟩ := h    -- n : ℕ, hn : n > 3
...
```

La diferencia fundamental entre utilizar el axioma de elección y utilizar `obtain` es que dos testigos obtenidos mediante obtain del mismo tipo (por ejemplo de tipo `∃ n : ℕ, n > 3`) no serán necesariamente iguales, mientras que si fueron obtenidos mediante `Classical.choose` siempre serán iguales.
