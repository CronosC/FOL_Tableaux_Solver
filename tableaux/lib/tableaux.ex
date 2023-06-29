
defmodule Tableaux do
  '''
  Assumptions:
    nary operators
    valid operators are:
      :not 1
      :and n
      :or n
    all operators are defined as:
        {:operator, [list of operands]}
        except not, which is:
        {:not, operand}
    Predicates are possible. They are defined in the same way:
        P(a, b) == {:P, [:a, :b]}
  '''

  '''
  Notes:
    - applying heuristic in each step is inefficient: change patterns s.t. beta always goes at the end, rest at the front?
  '''
  # Start the tableaux proof by contradiction
  def proof(expression, firsth\\&Function.identity/1, orderfunc\\&Enum.sort/1) do
    if wff?(expression) do
      expression = preprocess(expression, orderfunc)
      Tableaux.sat?([{:not, expression}], firsth)
    else
      IO.puts("Expression is invalid!")
      :error
    end
  end

  # all the preprocessing steps we do on the expression
  def preprocess(expression, orderfunc) do
    order(expression, orderfunc)
  end

  # orders all arguments of nary operators according to orderfunc
  def order(expression, orderfunc) do
    case expression do
      {f, x} when is_list(x) ->
        if operator?(f) do
          {f, Enum.map(x, fn x -> order(x, orderfunc) end)}
        else
          {f, x}
        end
      x -> x
    end
  end

  def remove_duplicates(expressions) do
    case expressions do
      [x | tail] -> if x in tail do remove_duplicates(tail) else [x] ++ remove_duplicates(tail) end
      [] -> []
    end
  end

  # Core tableaux method
  def sat?(expressions, firsth) do
    #IO.puts("#{inspect(self())}: #{inspect(expressions)}")
    # check abort condition (phi and not phi)
    if contradiction?(expressions) do
      #IO.puts("#{inspect(self())}: Contradiction found!")
      :false
    else
      # check if we can still apply more steps
      if done?(expressions) do
        #IO.puts("#{inspect(self())}: Can no longer apply any transformations!")
        :true
      else
        expressions = remove_duplicates(expressions)
        expressions = firsth.(expressions) # sorting heuristic
        # select fitting transformation step
        case expressions do
          # simple
          [:true | _] ->
            :true
          [:false | tail] ->
            sat?(tail, firsth)
          [{:not, :true} | tail] ->
            sat?(tail, firsth)
          [{:not, :false} | _] ->
            :true
          [{:not, {:not, phi}} | tail] ->
            sat?([phi] ++ tail, firsth)

          # alpha
          [{:and, operands} | tail] ->
            sat?(operands ++ tail, firsth)
          [{:not, {:or, operands}} | tail] ->
            sat?(negate(operands) ++ tail, firsth)

          # beta
          [{:or, operands} | tail] ->
            tasks = for op <- operands do
              do_async(fn -> sat?([op] ++ tail, firsth) end)
            end
            Enum.any?(tasks)
          [{:not, {:and, operands}} | tail] ->
            operands = negate(operands)
            tasks = for op <- operands do
              do_async(fn -> sat?([op] ++ tail, firsth) end)
            end
            Enum.any?(tasks)


          # else literal in front => ignore
          [x | tail] -> if atomic?(x) do sat?(tail ++ [x], firsth) else IO.puts("This should never occur! Missing case in sat.") end
        end
      end
    end
  end

  def negate(expressions) do
    case expressions do
      x when is_list(x) -> Enum.map(x, &negate/1)
      x -> {:not, x}
    end
  end

  # checks syntactic correctness of an expression
  def wff?(expression) do
    case expression do
      x -> if atomic?(x) do :true else
        case x do
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

  # checks if list of expressions contains the same expression, once with not in front and once without.
  def contradiction?(expressions) do
    case expressions do
      [] -> :false
      [{:not, phi} | tail] -> if phi in tail do :true else contradiction?(tail) end
      [phi | tail] -> if {:not, phi} in tail do :true else contradiction?(tail) end
    end
  end

  # checks if list of expressions only contains literals
  def done?(expressions) do
    case expressions do
      [] -> :true
      [x | tail] ->
        case atomic?(x) do
          :true -> done?(tail)
          :false -> :false
        end
    end
  end

  # checks if a list of expressions contains only finished or beta expressions
  def only_beta?(expressions) do
    case expressions do
      [] -> :true
      [x | tail] -> if atomic?(x) do
        only_beta?(tail)
      else
        (beta?(x) and only_beta?(tail))
      end
    end
  end

  # checks if an expression is a beta expression
  def beta?(expression) do
    case expression do
      {:or, _} -> :true
      {:not, {:and, _}} -> :true
      _ -> :false
    end
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

  # checks if something is in our approved operator list.
  def operator?(f) do
      f in [:not, :and, :or, :nand, :nor, :limp, :rimp, :nlimp, :nrimp]
  end

  # iterates over list of expressions and pulls alpha expressions to the front
  def alpha_first(expressions) do
    case expressions do
      [{:and, ops} | tail] -> [{:and, ops}] ++ tail
      [{:not, {:or, ops}} | tail] -> [{:not, {:or, ops}}] ++ tail
      [x | tail] -> alpha_first(tail) ++ [x]
      [] -> []
    end
  end

  # same as alpha first but instead pulls beta expressions to the end of the list
  def beta_last(expressions) do
    if only_beta?(expressions) do
      expressions
    else
      case expressions do
        [{:or, ops} | tail] -> beta_last(tail) ++ [{:or, ops}]
        [{:not, {:and, ops}} | tail] -> beta_last(tail) ++ [{:not, {:and, ops}}]
        [x | tail] -> [x] ++ tail
        [] -> []
      end
    end
  end

  # async call wrapper function
  def do_async(f) do
    Task.async(f)
  end

end

defmodule Helper do
  def timed_proof(expr) do
    IO.puts("Result: ")
    IO.inspect(Tableaux.proof(expr))
    IO.puts("Timings: ")
    IO.puts("as given: ")
    IO.inspect(Helper.time(fn -> Tableaux.proof(expr) end))
    IO.puts("randomized: ")
    IO.inspect(Helper.time(fn -> Tableaux.proof(expr, &Enum.shuffle/1) end))
    IO.puts("beta_last: ")
    IO.inspect(Helper.time(fn -> Tableaux.proof(expr, &Tableaux.beta_last/1) end))
    IO.puts("done!")
  end

  def timed_proofs(expressions) do
    IO.puts("number of expressions")
    IO.inspect(length(expressions))
    IO.puts("as given: ")
    IO.inspect(Helper.time(fn -> Enum.map(expressions, fn {x, _} -> Tableaux.proof(x) end) end))
    IO.puts("randomized: ")
    IO.inspect(Helper.time(fn -> Enum.map(expressions, fn {x, _} -> Tableaux.proof(x, &Enum.shuffle/1) end) end))
    IO.puts("beta_last: ")
    IO.inspect(Helper.time(fn -> Enum.map(expressions, fn {x, _} -> Tableaux.proof(x, &Tableaux.beta_last/1) end) end))
    #IO.puts("alpha_first: ")
    #IO.inspect(Helper.time(fn -> Enum.map(expressions, fn {x, _} -> Tableaux.proof(x, &Tableaux.alpha_first/1) end) end))
  end

  def time(function) do
    function
    |> :timer.tc
    |> elem(0)
    |> Kernel./(1_000_000)
  end
end
'''
[mode, file_arg | _] = System.argv()
case mode do
  "tptp" -> :pass
    #:leex.file('TPTP.xrl')
    #c("TPTP.erl")

    expression_file = "tptp/" <> file_arg
    {status, file_str} = File.read(expression_file)

    IO.inspect(file_str)

    {:ok, tokens, _} = :TPTP.string(file_str)
    IO.inspect(tokens)

  "txt" ->
    expression_file = "expressions/" <> file_arg <> ".txt"
    {status, file_str} = File.read(expression_file)


    case status do
      :error -> IO.puts("Could not read file!")
      _ ->
        expressions = String.split(file_str, "\n")
        expressions = Enum.map(expressions, fn x -> String.replace(x, "\r", "") end)
        expressions = Enum.map(expressions, fn x -> Code.eval_string(x) end)
        Helper.timed_proofs(expressions)
        #Enum.map(expressions, fn {x, _} -> Helper.timed_proof(x) end)
      end
end
'''
