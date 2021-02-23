***********
Type System
***********

.. math::
    \newcommand{\eff}{\iota}
    \newcommand{\pure}{{(|)}}

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

=======
Kinding
=======

``:`` is 'of type' and ``::`` is 'of kind'

There are builtin kinds (types) ``typeIn``, ``rowIn``, tuple types ``(:,)`` and
``array`` as well as type level arrays ``[,]`` and tuples ``(,)``.

axioms:

.. math::
    \begin{align*}
        \mathsf{singleRep} &= \mathsf{boxed} \; | \; \mathsf{word\{8, 16, 32, 64\}} \; | \;
            \mathsf{float\{32, 64\}} \\
        \mathsf{rep} &= \mathsf{array} \; \mathsf{singleRep} \\
        \mathsf{typeIn} &:: \mathsf{rep} \rightarrow \mathsf{type} \\
        \mathsf{type} &= \mathsf{typeIn} \; [\mathsf{boxed}] \\
        \mathsf{rowOf} &:: \mathsf{type} \rightarrow \mathsf{type} \\
        \mathsf{row} &= \mathsf{rowOf} \; \mathsf{type} \\
        [= \_] &:: \mathsf{type} \rightarrow \mathsf{typeIn} \; [] \\
        (\overline{e,}) &: (:\overline{\mathsf{typeof} \; e,}) \\
        (\overline{T,}) &:: \mathsf{typeIn} [\overline{\mathsf{repof} \; T,}] \\
        (\overline{\_,}) &:: \forall \overline{(r : \mathsf{rep})} . (:\overline{\mathsf{typeIn} \; r,})
            \rightarrow \mathsf{typeIn} \; [\overline{\mathsf{typeIn} \; r,}] \\
        (\_ \, -! \, \_ \rightarrow \_) &:: \forall (r1 : \mathsf{rep}) (r2 : \mathsf{rep})
            . (:\mathsf{typeIn} \; r1, \mathsf{row}, \mathsf{typeIn} \; r2) \rightarrow \mathsf{type}
    \end{align*}

=======
MLF-ing
=======

------------------------------------------------------------------------------------
Expression Type Synthesis :math:`\Gamma \vdash e \Rightarrow_\eff \Sigma \leadsto C`
------------------------------------------------------------------------------------

.. math::
    \frac{
        x : \Sigma \in \Gamma
    } {
        \Gamma \vdash x \Rightarrow_\pure \Sigma \leadsto \epsilon
    }

.. math::
    \frac{
        \Gamma, x : \hat{\alpha} \vdash e \Rightarrow_\eff \Sigma \leadsto C
    } {
        \Gamma \vdash \lambda x . e \Rightarrow_\pure \hat{\alpha} \rightarrow_\eff \Sigma \leadsto C
    }

.. math::
    \frac{
        \Gamma \vdash T \leadsto \exists \overline{\alpha} . \Sigma_d \\
        \Gamma, \overline{\alpha}, x : \Sigma_d \vdash e \Rightarrow_\eff \Sigma \leadsto C
    } {
        \Gamma \vdash \lambda x : T . e \Rightarrow_\pure
            \forall \overline{\alpha} . \Sigma_d \rightarrow_\eff \Sigma \leadsto \supset C
    }

.. math::
    \frac{
        \Gamma \vdash e_c \Leftarrow_{\eff_c} \hat{\alpha_d} \rightarrow \hat{\alpha_c} \leadsto C_c \\
        \Gamma \vdash e_a \Leftarrow_{\eff_a} \hat{\alpha_d} \leadsto C_a
    } {
        \Gamma \vdash e_c \, e_a \Rightarrow_\hat{\eff} \hat{\alpha_c}
            \leadsto
                C_c \wedge C_a \wedge
                \hat{\eff} \sim \eff_c \wedge \hat{\eff} \sim \eff_a
    }

.. math::
    \frac{
        \Gamma \vdash T \leadsto \exists \overline{\alpha} . \Sigma \\
        \overline{\alpha' \, \overline{\beta}} = hoist(\Gamma, \overline{\alpha}) \\
        \Sigma' = [\overline{\alpha' \, \overline{\beta}/\alpha}]\Sigma \\
        \Gamma \vdash e \Leftarrow_\eff \Sigma' \leadsto C \\
        \overline{\hat{\gamma}} = fuv(\Sigma_e) \cup fuv(C) - fuv(\Gamma)
    } {
        \Gamma \vdash (e : T) \Rightarrow_\eff \Sigma'
            \leadsto
                \exists \overline{\hat{\gamma}} . \overline{\alpha' \sim \hat{\alpha'}}
                    \supset C
    }

----------------------------------------------------------------------------------
Expression Type Checking :math:`\Gamma \vdash e \Leftarrow_\eff \Sigma \leadsto C`
----------------------------------------------------------------------------------

.. math::
    \frac{
        \Gamma \vdash e \Rightarrow_\eff \Sigma_e \leadsto C
    } {
        \Gamma \vdash e \Leftarrow_\eff \Sigma
            \leadsto
                C \wedge \hat{\beta} \geq \Sigma_e \wedge \hat{\beta} \sim \Sigma
    }

