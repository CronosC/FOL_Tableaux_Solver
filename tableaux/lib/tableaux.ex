
defmodule Tableaux do
  '''
  Assumptions:
    nary operators
    valid operators are:
      :not/1
      :and/n
      :or/n
    all operators are defined as:
        {:operator, [list of operands]}
        except not, which is:
        {:not, operand}
    Variables are uppercase, constants lowercase.
    Predicates are possible. They are defined in the same way as operators:
        P(a, b) == {:P, [:a, :b]}
    Quantifiers are possible:
        \forall x, y : phi == {:allqu, [x, y], phi}
        \existence x : phi == {:exqu, [x], phi}
  '''


  '''
  Notes:
    x some tests
    x see notes in logic (unify)
    - instantiation method
    - find bug in tableaux
    x Signature explizit machen
    - tableaux with unification?  =>> copy whole tableaux for each unification?
    - resolution with unification?
    - applying heuristic in each step is inefficient: change patterns s.t. beta always goes at the end, rest at the front?
  '''

  # Start the tableaux proof by contradiction
  def proof(expression, firsth\\&Function.identity/1, orderfunc\\&Enum.sort/1) do
    if Logic.wff?(expression) do
      expression = PrePro.preprocess(expression, orderfunc)
      not Tableaux.sat?([{:not, expression}], firsth)
    else
      IO.puts("Expression is invalid!")
      :error_invalid_expression
    end
  end

  # Core tableaux method
  def sat?(expressions, firsth) do
    #IO.puts("#{inspect(self())}: #{inspect(expressions)}")
    #IO.inspect(expressions)
    # check abort condition (phi and not phi)
    if contradiction?(expressions) do
      #IO.puts("#{inspect(self())}: Contradiction found!")
      :false
    else
      # check if we can still apply more steps
      if done?(expressions) do
        #IO.puts("#{inspect(self())}: Can no longer apply any transformations!")
        #IO.inspect(expressions)
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
            sat?(tail ++ operands, firsth)
          [{:not, {:or, operands}} | tail] ->
            sat?(tail ++ Logic.negate(operands), firsth)

          # beta
          [{:or, operands} | tail] ->
            '''
            tasks = for op <- operands do
              do_async(fn -> sat?([op] ++ tail, firsth) end)
            end
            Enum.any?(tasks)
            '''
            Enum.any?(Enum.map(operands, fn x -> sat?(tail ++ [x], firsth) end))

          [{:not, {:and, operands}} | tail] ->
            operands = Logic.negate(operands)
            '''
            tasks = for op <- operands do
              do_async(fn -> sat?([op] ++ tail, firsth) end)
            end
            Enum.any?(tasks)
            '''
            Enum.any?(Enum.map(operands, fn x -> sat?(tail ++ [x], firsth) end))


          # else literal in front => ignore
          [x | tail] -> if Logic.atomic?(x) do sat?(tail ++ [x], firsth) else :error_missing_case end
        end
      end
    end
  end

  # removes duplicate expressions from the expression list
  def remove_duplicates(expressions) do
    case expressions do
      [x | tail] -> if x in tail do remove_duplicates(tail) else [x] ++ remove_duplicates(tail) end
      [] -> []
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

  # checks if list of expressions only contains atomic expressions
  def done?(expressions) do
    case expressions do
      [] -> :true
      [x | tail] ->
        case Logic.atomic?(x) do
          :true -> done?(tail)
          :false -> :false
        end
    end
  end

  # checks if a list of expressions contains only finished or beta expressions
  def only_beta?(expressions) do
    case expressions do
      [] -> :true
      [x | tail] -> if Logic.atomic?(x) do
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
