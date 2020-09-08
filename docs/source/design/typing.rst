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

