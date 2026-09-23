from execution.sol_compilation import SolidityCompilation


def _compilation():
    return SolidityCompilation(None, "solc")


class TestProcessJsonOutput:
    def test_builds_the_file_contract_structure_alongside_the_flattened_dict(self):
        output_dict = {
            "contracts": {
                "a.sol": {"A": {"yulCFGJson": {"type": "Object", "A": {}}}},
                "b.sol": {"B": {"yulCFGJson": {"type": "Object", "B": {}}}},
            },
        }
        compilation = _compilation()

        correct, json_dict = compilation._process_json_output(output_dict, "", None)

        assert correct is True
        assert json_dict == {"A": {"type": "Object", "A": {}}, "B": {"type": "Object", "B": {}}}
        assert compilation.last_contract_structure == {"a.sol": ["A"], "b.sol": ["B"]}

    def test_excludes_a_contract_with_a_null_yulcfgjson_from_both_the_dict_and_the_structure(self):
        output_dict = {
            "contracts": {
                "a.sol": {"A": {"yulCFGJson": None}, "Interface": {"yulCFGJson": {"type": "Object"}}},
            },
        }
        compilation = _compilation()

        _, json_dict = compilation._process_json_output(output_dict, "", None)

        assert "A" not in json_dict
        assert compilation.last_contract_structure == {"a.sol": ["Interface"]}

    def test_resets_the_structure_on_a_compile_error(self):
        compilation = _compilation()
        compilation.last_contract_structure = {"stale.sol": ["Stale"]}
        output_dict = {"errors": [{"severity": "error", "message": "boom"}], "contracts": {}}

        correct, json_dict = compilation._process_json_output(output_dict, "", None)

        assert correct is False
        assert compilation.last_contract_structure == {}
