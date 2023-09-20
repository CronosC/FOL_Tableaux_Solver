defmodule Parser do
  @moduledoc """
  leex and yecc based parser for the TPTP language.
  """
  def parse_KR() do
    parse_file("../data/tptp/cnf_sat/KRS005-1.p")
  end

  def lex(str) do
    :TPTP_lexer.string(to_charlist(str))
  end

  def parse_tokens(tokens) do
    :TPTP_parser.parse(tokens)
  end

  def parse(str) do
    {errorcode_lex, tokens, _} = :TPTP_lexer.string(to_charlist(str))
    case errorcode_lex do
      :ok ->
        #IO.inspect(tokens)
        {errorcode_parse, expression} = :TPTP_parser.parse(tokens)
        case errorcode_parse do
          :ok ->
            #IO.puts("Parsing successful!")
            expression
          _ ->
            IO.puts("Error parsing tokens!")
            :error_parsing
        end
      _ ->
        IO.puts("Error lexing string!")
        :error_lexing
    end
  end

  def parse_file(path) do
    {errorcode_read, file_str} = File.read(path)
    case errorcode_read do
      :ok -> parse(file_str)
      _ ->
        IO.puts("Error reading file!")
        :error_read_file
    end
  end
end
