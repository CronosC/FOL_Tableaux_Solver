defmodule Helper do

  def test_all(type) do
    dir = "../data/tptp/" <> type <> "/"
    {:ok, dir_contents} = File.ls(dir)
    files = Enum.map(dir_contents, fn x -> File.read(dir <> x)end)
    IO.puts("Read files..")
    expressions = Enum.map(files, fn {:ok, x} ->Parser.parse(x)end)
    IO.puts("Parsed files..")
    results = Enum.map(expressions, fn x -> Tableaux.proof(x, false) end)
    IO.inspect(Enum.zip(dir_contents, results))
    results
  end

  def proof(file) do
    expr = Parser.parse_file(file)
    Tableaux.proof(expr)
  end
  def proof_KR() do
    proof("../data/tptp/cnf_sat/KRS005-1.p")
  end

  def proof_LCL() do
    proof("../data/tptp/cnf_unsat/LCL117-1.p")
  end


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
