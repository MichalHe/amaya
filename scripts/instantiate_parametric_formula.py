import argparse
import sys
import os


def load_parameter_values(param_values_path):
    with open(param_values_path) as values_file:
        for line in values_file.read().split('\n'):
            line = line.strip()
            if line:
                yield int(line)


def instantiate_formula(template_text: str, parameter_name: str, parameter_value: int):
    key = f'${{{parameter_name}}}'
    template_text = template_text.replace(key, str(parameter_value))
    return template_text


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('formula_template_file')
    parser.add_argument('parameter_name', help='Name of the parameter to substitute')
    parser.add_argument('parameter_values')
    parser.add_argument('output_folder')
    args = parser.parse_args()

    with open(args.formula_template_file) as template_file:
        template_text = template_file.read()

    if not os.path.isdir(args.output_folder):
        print('The output folder does not exists!')
        sys.exit(1)

    template_filename = os.path.basename(args.formula_template_file)
    filename, ext = template_filename.rsplit('.', maxsplit=1)
    instance_filename_template = f'{filename}_{{0}}.{ext}'

    for param_value in load_parameter_values(args.parameter_values):
        formula = instantiate_formula(template_text, args.parameter_name, param_value)
        output_filename = instance_filename_template.format(f'{args.parameter_name}({param_value})')
        output_path = os.path.join(args.output_folder, output_filename)

        with open(output_path,  'w') as output_file:
            output_file.write(formula)
