defmodule PrePro do

  # all the preprocessing steps we do on the expression
  @spec preprocess(any, any) :: any
  def preprocess(expression, orderfunc\\&Enum.sort/1) do
    preprocess_quantifiers(order(expression, orderfunc))
  end

  # orders all arguments of nary operators according to orderfunc
  def order(expression, orderfunc) do
    case expression do
      {q, v, x} -> {q, v, order(x, orderfunc)}
      {f, x} when is_list(x) ->
        if Logic.operator?(f) do
          {f, Enum.map(x, fn x -> order(x, orderfunc) end)}
        else
          {f, x}
        end
      {:not, x} -> {:not, order(x, orderfunc)}
      x -> x
    end
  end

  # transforms all quantified variables into a new namespace with qVar_ in front
  # Hopefully prevents collisions at a later date
  def preprocess_quantifiers(expression) do
    case expression do
      {q, v, phi} when is_list(v) ->
        theta = get_substitution_for_quantified_vars(v)
        {q, Logic.substitute(v, theta), preprocess_quantifiers(Logic.substitute(phi, theta))}
      {f, x} when is_list(x) -> {f, Enum.map(x, fn x -> preprocess_quantifiers(x) end)}
      {f, phi} -> {f, preprocess_quantifiers(phi)}
      x -> x
    end
  end

  # Creates a substitution (map) of a list of variables s.t. all get qVar_ as prefix
  # [:X, :Y] ==> %{:X => :qVar_X, :Y => :qVar_Y}
  def get_substitution_for_quantified_vars(varlist) do
    case varlist do
      [v | []] -> %{v => String.to_atom("qVar_" <> Atom.to_string(v))}
      [v | vs] -> Map.merge(%{v => String.to_atom("qVar_" <> Atom.to_string(v))}, get_substitution_for_quantified_vars(vs))
    end
  end
end
