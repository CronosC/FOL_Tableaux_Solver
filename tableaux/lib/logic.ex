defmodule Logic do

  # checks syntactic correctness of an expression
  def wff?(expression) do
    case expression do
      x -> if atomic?(x) do :true else
        case x do
          {:allqu, v, x} -> if Enum.all?(Enum.map(v, &atomic?/1)) do wff?(x) else :false end
          {:exqu, v, x} -> if Enum.all?(Enum.map(v, &atomic?/1)) do wff?(x) else :false end
          {:not, x} -> wff?(x)
          {:and, ops} -> if length(ops) >= 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          {:or, ops} -> if length(ops) >= 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          {:nand, ops} -> if length(ops) >= 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          {:nor, ops} -> if length(ops) >= 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          {:rimp, ops} -> if length(ops) == 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          {:limp, ops} -> if length(ops) == 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          {:nrimp, ops} -> if length(ops) == 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          {:nlimp, ops} -> if length(ops) == 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          x -> IO.puts("Forgotten case in wff?!")
               IO.inspect(x)
               :false
        end
      end
    end
  end

  # checks if something is in our approved operator list.
  def operator?(f) do
      f in [:not, :and, :or, :nand, :nor, :limp, :rimp, :nlimp, :nrimp]
  end

  # checks if some expression is atomic. Includes predicates.
  def atomic?(expression) do
    case expression do
      {:not, x} -> atomic?(x)
      {f, x} when is_list(x) -> (not operator?(f)) and Enum.all?(Enum.map(x, &atomic?/1))
      {f, x} -> (not operator?(f)) and atomic?(x)
      x when is_atom(x) -> not operator?(x)
    end
  end

  # negates an expression
  def negate(expressions) do
    case expressions do
      x when is_list(x) -> Enum.map(x, &negate/1)
      {:not, x} -> x
      x -> {:not, x}
    end
  end

  # theta is a substitution map, the method looks for occurences of keys of theta in formula and replaces them with the assosiacted values
  def substitute(formula, theta) do
    case formula do
      {q, v, x} -> {q, v, substitute(x, theta)}
      {f, x} -> {f, substitute(x, theta)}
      x when is_list(x) -> Enum.map(x, fn x -> substitute(x, theta) end)
      x when is_map_key(theta, x) -> theta[x]
      x -> x
    end
  end

end
