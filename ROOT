session "compcertSSA" = "FormalSSA" +
theories
  Generic_Extract

chapter AFP

session "FormalSSA_base" (AFP) = "Collections" +
theories
  "~~/src/HOL/Library/While_Combinator"
  "~~/src/HOL/Library/Product_Lexorder"
  "~~/src/HOL/Library/Sublist"
  "~~/src/HOL/Library/RBT_Set"
  "~~/src/HOL/Library/RBT_Mapping"
  "~~/src/HOL/Library/Char_ord"
  "~~/src/HOL/Library/List_lexord"
  "~~/src/HOL/Library/Code_Target_Numeral"
  "$AFP/Slicing/While/AdditionalLemmas"
  "$AFP/Dijkstra_Shortest_Path/GraphSpec"

session "FormalSSA" (AFP) = "FormalSSA_base" +
options[document=pdf,  document_output=output]
theories
  FormalSSA_Misc
  Serial_Rel
  Mapping_Exts
  RBT_Mapping_Exts
  SSA_CFG
  Minimality
  Construct_SSA
  Construct_SSA_notriv
  SSA_Semantics
  While_Combinator_Exts
  Construct_SSA_code
  Construct_SSA_notriv_code
  Generic_Interpretation
  WhileGraphSSA
document_files
  "root.tex"
  "root.bib"
