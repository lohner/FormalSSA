set style data linespoints
g(x) = a*x**b*log(x)**c
h(x) = d*x**e*log(x)**f
a=1e-7;b=1;c=2
d=1e-7;e=1;f=2
fit g(x) "ifplot_with_cytron.data" using 1:2 via a, b, c
fit h(x) "ifplot_with_cytron.data" using 1:3 via d, e, f
plot "ifplot_with_cytron.data" using 1:2 title "Cytron", "ifplot_with_cytron.data" using 1:3 title "Braun", g(x) title sprintf("Cytron-Fit: %.2g * n^{%.2g} * lg(n)^{%.2g}", a, b, c), h(x) title sprintf("Braun-Fit: %.2g * n^{%.2g} * lg(n)^{%.2g}", d, e, f)
