***********
Type System
***********

.. math::
    \newcommand{\eff}{\iota}
    \newcommand{\pure}{{(||)}}

.. math::
    \frac{
        x : \Sigma \in \Gamma
    }{
        \Gamma \vdash x \Rightarrow_\pure \Sigma \dashv \Gamma
    }

.. math::
    \frac{
        \Gamma \vdash e_f \Rightarrow_{\eff_f} \Sigma_f \dashv \Theta \\
        \Theta \vdash \Sigma_f \gg \_ \rightarrow \_
            \leadsto \overline{\Sigma_I} \; \overline{\Sigma_d} \rightarrow_{\eff_c} \Sigma_c
            \dashv \Theta \\
        \#\overline{\Sigma_d} = \#\overline{e_a} \\
        \Theta' \vdash \eff_c \sim \eff_f \dashv \Theta_0 \\
        \Theta_{i - 1} \vdash e_{a, i} \Leftarrow_{\eff_{a, i}} [\Theta_{i - 1}]\hat{\alpha}_i
            \dashv \Theta_i' \leadsto C_i \\
        \Theta_i' \vdash \eff_{a, i} \sim \eff_f \dashv \Theta_i
    }{
        \Gamma \vdash e_f \; \overline{e_a} \Rightarrow_{\eff_f} [\Delta]\hat{\beta}
            \dashv \delta
    }

.. math::
    \frac{
        \Gamma \vdash e \Leftarrow_\eff \{|\hat{\rho} \; \mathsf{with} \; x : \hat{\alpha}|\}
            \dashv \Delta
    }{
        \Gamma \vdash e.x \Rightarrow_\eff [\Delta]\hat{\alpha} \dashv \Delta
    }

.. math::
    \frac{}{\Gamma \vdash n \Rightarrow_\pure \mathsf{\_\_int} \dashv \Gamma}

-------
Kinding
-------

``:`` is 'of type' and ``::`` is 'of kind'

There are builtin kinds (types) ``typeIn``, ``row`` and ``array``.

axioms:

.. math::
    \begin{align*}
        \mathsf{singleRep} &= \mathsf{boxed} \; | \; \mathsf{word\{8, 16, 32, 64\}} \; | \;
            \mathsf{float\{32, 64\}} \\
        \mathsf{rep} &= \mathsf{array} \; \mathsf{singleRep} \\
        \mathsf{typeIn} &:: \mathsf{rep} \rightarrow \mathsf{type} \\
        \mathsf{row} &:: \mathsf{type} \\
        \mathsf{type} &= \mathsf{typeIn} \; [\mathsf{boxed}] \\
        [= \_] &:: \mathsf{type} \rightarrow \mathsf{typeIn} \; [] \\
        (\overline{e,}) &: (\overline{\mathsf{typeof} \; e,}) \\
        (\overline{T,}) &:: \mathsf{typeIn} [\overline{\mathsf{repof} \; T,}] \\
        (\overline{\_,}) &:: \forall \overline{(r : \mathsf{rep})} . (\overline{\mathsf{typeIn} \; r,})
            \rightarrow \mathsf{typeIn} \; [\overline{\mathsf{typeIn} \; r,}] \\
        (\_ \, -! \, \_ \rightarrow \_) &:: \forall (r1 : \mathsf{rep}) (r2 : \mathsf{rep})
            . (\mathsf{typeIn} \; r1, \mathsf{row}, \mathsf{typeIn} \; r2) \rightarrow \mathsf{type}
    \end{align*}

