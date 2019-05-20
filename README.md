# taes-project
(*This repository contains the Coq specification files for the theory of Software Product Line Refinement*)

Software Product Line (SPL) are families of software products where similar products are
created from a common feature, maximizing software reuse, reducing development costs,
enhancing the quality of the developed products. They are formally represented as a triple: (i)
a feature model that contains features and dependencies among them, (ii) an asset mapping,
that contains sets of assets and asset names, (iii) a configuration knowledge, that allows
features to be related to assets.
There are several challenges in the SPL development context. SPLs tend to increase
over time, and the larger a SPL becomes, the higher is the complexity to evolve it. When
evolving, in some cases, it is desirable to provide some assurance that we can safely change a
SPL in the sense that the behaviour of existing products is preserved after the change. For
this, it is important to have a notion of product line refinement that assures behavior
preservation of the original product line products. The theory of product line refinement
formalizes this notion. To specify and prove soundness of the theories, this work describes an
effort to formalize them using the Coq proof assistant.
