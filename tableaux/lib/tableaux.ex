
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
    x instantiation method
    - all quantor: dont instantiate new constant, unless no constants in signature
    - additionally: Create any valid closed term from signature and instantiate it (all quantor)
    - done check from beginning to end
    - all quantor elimination via free variables
    - find bug in tableaux
    x Signature explizit machen
    - tableaux with unification?  =>> copy whole tableaux for each unification?
      - unification only when we can close tableaux (or all unifications on that branch!)
      - then restart whole tableaux with that substitution applied (as or)
    - resolution with unification?
    - applying heuristic in each step is inefficient: change patterns s.t. beta always goes at the end, rest at the front?
  '''

  # Start the tableaux proof by contradiction
  @spec proof(atom | maybe_improper_list | {any, any} | {any, any, any}, any, any) ::
          :error_invalid_expression | false | true
  def proof(expression, negate\\true, maxdepth\\999999999, firsth\\&Function.identity/1, orderfunc\\&Enum.sort/1) do
    if Logic.wff?(expression) do
      expression = PrePro.preprocess(expression, orderfunc)
      signature = Logic.get_Signature(expression)
      if negate do
        #IO.inspect({:not, expression})
        not Tableaux.sat?([{:not, expression}], firsth, signature, maxdepth)
      else
        #IO.inspect(expression)
        Tableaux.sat?([expression], firsth, signature, maxdepth)
      end
    else
      IO.puts("Expression is invalid!")
      :error_invalid_expression
    end
  end

  # Core tableaux method
  def sat?(expressions, firsth, sig, maxdepth\\9999999) do
    if maxdepth <= 0 do
      IO.puts("Reached max depth, assuming sat..")
      IO.inspect(expressions)
      :true
    else
      #IO.puts("#{inspect(self())}: #{inspect(expressions)}")
      #IO.inspect(maxdepth)
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
          #IO.puts("Can no longer apply any transformation steps => sat!")
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
              sat?(tail, firsth, sig, maxdepth - 1)
            [{:not, :true} | tail] ->
              sat?(tail, firsth, sig, maxdepth - 1)
            [{:not, :false} | _] ->
              :true
            [{:not, {:not, phi}} | tail] ->
              sat?([phi] ++ tail, firsth, sig, maxdepth - 1)

            # alpha
            [{:and, operands} | tail] ->
              sat?(tail ++ operands, firsth, sig, maxdepth - 1)
            [{:not, {:or, operands}} | tail] ->
              sat?(tail ++ Logic.negate(operands), firsth, sig, maxdepth - 1)

            # beta
            [{:or, operands} | tail] ->
              '''
              tasks = for op <- operands do
                do_async(fn -> sat?([op] ++ tail, firsth, maxdepth - 1) end)
              end
              Enum.any?(tasks)
              '''
              Enum.any?(Enum.map(operands, fn x -> sat?(tail ++ [x], firsth, sig, maxdepth - 1) end))

            [{:not, {:and, operands}} | tail] ->
              operands = Logic.negate(operands)
              '''
              tasks = for op <- operands do
                do_async(fn -> sat?([op] ++ tail, firsth, maxdepth - 1) end)
              end
              Enum.any?(tasks)
              '''
              Enum.any?(Enum.map(operands, fn x -> sat?(tail ++ [x], firsth, sig, maxdepth - 1) end))

            # gamma: instantiate existence quantors with new constants
            [ {:exqu, v, x} | tail ] ->
              theta = instantiate_parameters(v, sig)
              new_expressions = [Logic.substitute(x, theta)] ++ tail
              new_sig = Logic.get_Signature(new_expressions)
              sat?(new_expressions, firsth, new_sig, maxdepth - 1)
            [ {:not, {:allqu, v, x}} | tail ] -> sat?([{:exqu, v, {:not, x}}] ++ tail , firsth, sig, maxdepth - 1)

            # delta
            [ {:allqu, v, x} | tail ] ->
              chosen_var = Enum.random(v)
              theta = instantiate_terms([chosen_var], sig)
              if length(v) > 1 do
                filtered_v = for a when a != chosen_var <- v, do: a
                new_expressions =  tail ++ [{:allqu, filtered_v, Logic.substitute(x, theta)}] ++ [{:allqu, v, x}]
                new_sig = Logic.get_Signature(new_expressions)
                sat?(new_expressions, firsth, new_sig, maxdepth - 1)
              else
                new_expressions = tail ++ [Logic.substitute(x, theta)] ++ [{:allqu, v, x}]
                new_sig = Logic.get_Signature(new_expressions)
                sat?(new_expressions, firsth, new_sig, maxdepth - 1)
              end
            [ {:not, {:exqu, v, x}} | tail ] -> sat?([{:allqu, v, {:not, x}}] ++ tail , firsth, sig, maxdepth - 1)

            # else literal in front => ignore
            [x | tail] ->
              if Logic.atomic?(x) do
                sat?(tail ++ [x], firsth, sig, maxdepth - 1)
              else :error_missing_case
            end
          end
        end
      end
    end
  end

  def instantiate_terms(varlist, sig) do
    case varlist do
      [] -> %{}
      [v | vs] ->
        new_term = create_term(sig)
        Map.merge(%{v => new_term}, instantiate_terms(vs, sig))
    end
  end

  def create_term(sig, max_recursion\\2) do
    if max_recursion <= 0 do
      Enum.random(sig[:Constants])
    else
      choices = sig[:Constants] ++ sig[:Relations]
      choice = Enum.random(choices)
      case choice do
        {f, a} ->
          arguments = Enum.map(1..a, fn(_) -> create_term(sig, max_recursion - 1) end)
          {f, arguments}
        c -> c
      end
    end
  end

  # Creates a substitution map for new constants given a variable list.
  def instantiate_parameters(varlist, sig) do
    case varlist do
      [] -> %{}
      [v | vs] ->
        new_c = get_new_constants(sig)
        new_sig = %{sig | :Constants => (sig[:Constants] ++ [new_c])}
        Map.merge(%{v => new_c}, instantiate_parameters(vs, new_sig))
    end
  end

  # creates a new atom representing a constant given a signature.
  def get_new_constants(sig) do
    rand_const = String.to_atom("p_" <> for _ <- 1..5, into: "", do: <<Enum.random(?a..?z)>>)
    if rand_const in sig[:Constants] do
      get_new_constants(sig) # retry
    else
      rand_const
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
      [{:not, phi} | tail] -> if phi in tail do
        IO.puts("Contradiction found!")
        IO.inspect(phi)
        IO.inspect({:not, phi})
        :true
      else contradiction?(tail) end
      [phi | tail] -> if {:not, phi} in tail do
        IO.puts("Contradiction found!")
        IO.inspect(phi)
        IO.inspect({:not, phi})
        :true
      else contradiction?(tail) end
    end
  end

  # checks if list of expressions only contains atomic expressions
  def done?(expressions) do
    Logic.atomic?(expressions)
  end

  #@spec done?(maybe_improper_list) :: boolean
  def done_old(expressions) do
    case expressions do
      [] ->
        :true
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
