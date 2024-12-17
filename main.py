import re
from collections import defaultdict, deque
from itertools import product
import random


def read_grammar_from_file(filename):
    lines = []
    try:
        with open(filename, 'r') as f:
            lines = f.readlines()
        lines = [line.strip() for line in lines if line.strip()]
    except FileNotFoundError:
        print(f"Файл {filename} не найден.")
    return lines


def write_test_results(filename, test_results):
    try:
        with open(filename, 'w') as f:
            for result in test_results:
                f.write(f"{result[0]} {'1' if result[1] else '0'}\n")
    except FileNotFoundError:
        print(f"Файл {filename} не найден.")


def generate_and_test(grammar, terminals, first, test_count, start, randomness_prob):
    test_results = []
    nTs = extract_non_terminals(cnf_grammar)
    for _ in range(test_count):
        generated_string = generate_string(bigramms, terminals, first, start, randomness_prob)
        is_valid = cyk(grammar, start, generated_string)
        test_results.append((generated_string, is_valid))
    return test_results


def test_string(string, grammar, start):
    is_valid = cyk(grammar, start, string)
    if is_valid:
        print(f"Строка '{string}' ПРИНАДЛЕЖИТ грамматике.")
    else:
        print(f"Строка '{string}' НЕ ПРИНАДЛЕЖИТ грамматике.")


def my_print(g):
    for lhs, rules in g.items():
        print(f"{lhs} -> {' | '.join(' '.join(rule) for rule in rules)}")
    print("\n")


def get_brackets(s):
    pattern = r'\[[A-Za-z0-9]+\]|[A-Z][0-9]?|[a-z]'
    matches = re.findall(pattern, s)
    return matches


def parse(lines):
    rules = []
    nonTerms = defaultdict(list)

    for rule in lines:
        # Разделяем правило на левую и правую части
        lhs, rhs = rule.strip().split('->')
        lhs = lhs.strip()

        # Преобразуем правую часть
        rhs = get_brackets(rhs.strip())  # Извлекаем элементы правила

        # Для корректности определяем терминалы и нетерминалы
        processed_rhs = []
        for symbol in rhs:
            processed_rhs.append(symbol)

        rules.append((lhs, processed_rhs))

    # Формируем словарь правил
    for lhs, rhs in rules:
        nonTerms[lhs].append(rhs)

    return nonTerms


def remove_long_rules(grammar):
    new_grammar = defaultdict(list)
    counter = 1

    for lhs, rules in grammar.items():
        for rule in rules:
            if len(rule) <= 2:
                new_grammar[lhs].append(rule)
            else:
                current_lhs = lhs
                for i in range(len(rule) - 2):
                    new_nonterminal = f"_!{counter}"
                    counter += 1
                    new_grammar[current_lhs].append([rule[i], new_nonterminal])
                    current_lhs = new_nonterminal
                new_grammar[current_lhs].append(rule[-2:])

    return new_grammar


def remove_chain_rules(grammar):
    # Словарь для хранения информации о цепных правилах
    has_chain_to = {nt: set() for nt in grammar}

    # Вычисление множества "родительских" нетерминалов
    for nt in grammar:
        # Добавляем нетерминалы, к которым можно перейти напрямую
        has_chain_to[nt] = {B for B, rules in grammar.items() if [nt] in rules}

        # Рекуррентное вычисление всех переходов через цепные правила
        def next_set():
            return {C for C, rules in grammar.items() for D in has_chain_to[nt] if [D] in rules} | has_chain_to[nt]

        while has_chain_to[nt] != next_set():
            has_chain_to[nt] = next_set()

    # Добавление правил для всех связанных нетерминалов
    for child_nt, parents in has_chain_to.items():
        for parent_nt in parents:
            grammar[parent_nt].extend([rule for rule in grammar[child_nt] if rule not in grammar[parent_nt]])

    # Удаление цепных правил
    for nt, alternatives in grammar.items():
        grammar[nt] = [alt for alt in alternatives if not (len(alt) == 1 and alt[0] in grammar)]

    return grammar


def remove_useless_symbols(grammar, start_symbol):
    # Шаг 1. Определяем порождающие нетерминалы
    generating = set()
    changed = True

    # Шаг 1.1. Добавляем нетерминалы, которые порождают только терминалы
    while changed:
        changed = False
        for non_term, rules in grammar.items():
            if non_term in generating:
                continue
            for rule in rules:
                if all((symbol.islower() and symbol[0] != '[') for symbol in rule) or all(
                        symbol in generating or (symbol.islower() and symbol[0] != '[') for symbol in rule):
                    generating.add(non_term)
                    changed = True
                    break

    # Удаляем правила с непорождающими нетерминалами
    grammar = {
        non_term: [
            rule for rule in rules
            if all(symbol in generating or (symbol.islower() and symbol[0] != '[') for symbol in rule)
        ]
        for non_term, rules in grammar.items()
        if non_term in generating
    }

    # Шаг 2. Определяем достижимые нетерминалы
    reachable = set([start_symbol])
    queue = deque([start_symbol])

    while queue:
        current = queue.popleft()
        for rule in grammar.get(current, []):
            for symbol in rule:
                if ((not symbol.islower()) or len(symbol) > 1) and symbol not in reachable:  # Если символ — нетерминал
                    reachable.add(symbol)
                    queue.append(symbol)

    # Удаляем правила с недостижимыми нетерминалами
    grammar = {
        non_term: [
            rule for rule in rules
            if all(symbol in reachable or (symbol.islower() and symbol[0] != '[') for symbol in rule)
        ]
        for non_term, rules in grammar.items()
        if non_term in reachable
    }
    return grammar


def replace_terminals(grammar):
    """Заменяет все терминалы в длинных правилах на нетерминалы."""
    terminal_map = {}
    new_grammar = defaultdict(list)
    counter = 1

    for lhs, rules in grammar.items():
        for rule in rules:
            if len(rule) > 1:
                new_rule = []
                for symbol in rule:
                    if symbol.islower() and symbol[0] != '[':
                        if symbol not in terminal_map:
                            new_nonterminal = f"!_{counter}"
                            counter += 1
                            terminal_map[symbol] = new_nonterminal
                            new_grammar[new_nonterminal].append([symbol])
                        new_rule.append(terminal_map[symbol])
                    else:
                        new_rule.append(symbol)
                new_grammar[lhs].append(new_rule)
            else:
                new_grammar[lhs].append(rule)

    return new_grammar


def convert_to_cnf(grammar, start):
    grammar = remove_long_rules(grammar)
    grammar = remove_chain_rules(grammar)
    grammar = remove_useless_symbols(grammar, start)
    grammar = replace_terminals(grammar)
    return grammar


def build_first(grammar):
    first = defaultdict(set)

    # Инициализация FIRST для терминалов
    for lhs, rules in grammar.items():
        for rule in rules:
            for symbol in rule:
                if symbol.islower() and symbol[0] != '[':  # Терминал
                    first[lhs].add(symbol)
                    break

    # Повторяем до тех пор, пока FIRST не перестанет изменяться
    changed = True
    while changed:
        changed = False
        for lhs, rules in grammar.items():
            for rule in rules:
                for symbol in rule:
                    if ((not symbol.islower()) or len(symbol) > 1):  # Нетерминал
                        new_first = first[symbol] - first[lhs]
                        if new_first:
                            first[lhs].update(new_first)
                            changed = True
                    break

    return first


def build_follow(grammar, first):
    follow = defaultdict(set)
    follow[start].add('$')  # Начальный символ всегда имеет конец строки в FOLLOW

    # Повторяем до тех пор, пока FOLLOW не перестанет изменяться
    changed = True
    while changed:
        changed = False
        for lhs, rules in grammar.items():
            for rule in rules:
                for i in range(len(rule)):
                    if ((not rule[i].islower()) or rule[i][0] == '['):  # Нетерминал
                        if i == len(rule) - 1:  # Если нет символов после
                            new_follow = follow[lhs]
                            if new_follow - follow[rule[i]]:
                                follow[rule[i]].update(new_follow)
                                changed = True
                        else:
                            new_first = first[rule[i + 1]] - {'ε'}
                            if new_first - follow[rule[i]]:
                                follow[rule[i]].update(new_first)
                                changed = True

    return follow


def reverse_grammar(grammar):
    reversed_grammar = defaultdict(list)
    for lhs, rules in grammar.items():
        for rule in rules:
            reversed_grammar[lhs].append(list(reversed(rule)))
    return reversed_grammar


def build_last(grammar):
    copy_grammar = grammar.copy()
    rev_grammar = reverse_grammar((copy_grammar))
    last = build_first(rev_grammar)
    return last


def build_precede(grammar, first):
    copy_grammar = grammar.copy()
    rev_grammar = reverse_grammar((copy_grammar))
    precede = build_follow(rev_grammar, first)
    return precede


def extract_terminals(grammar):
    terminals = set()
    for non_terminal, productions in grammar.items():
        for production in productions:
            for symbol in production:
                if symbol.islower() and symbol[0] != '[':
                    terminals.add(symbol)
    return terminals


def extract_non_terminals(grammar):
    nTs = set()

    for nT, rules in grammar.items():
        nTs.add(nT)
        for rule in rules:
            for symbol in rule:
                if (not symbol.islower()) or len(symbol) > 1 or len(symbol) > 1:
                    nTs.add(symbol)

    return nTs


def build_bigramms(grammar, terminals, FIRST, FOLLOW, LAST, PRECEDE):
    bigram_matrix = defaultdict(set)

    # Собираем все правила в единый список
    extended_rules = []
    for rules in grammar.values():
        extended_rules.extend(rules)

    # Проход по всем возможным парам терминалов
    for y1 in terminals:
        for y2 in terminals:
            # Проверка на наличие пары (y1, y2) в правых частях правил
            pair_exists = False
            for rule in extended_rules:
                for i in range(len(rule) - 1):
                    if (y1, y2) == (rule[i], rule[i + 1]):
                        pair_exists = True
                        break
                if pair_exists:
                    break

            if pair_exists:
                bigram_matrix[y1].add(y2)

            condition_1 = any(y1 in LAST[nt] and y2 in FOLLOW[nt] for nt in grammar)
            condition_2 = any(y1 in PRECEDE[nt] and y2 in FIRST[nt] for nt in grammar)
            condition_3 = any(
                y1 in LAST[nt1] and y2 in FIRST[nt2] and y2 in FOLLOW[nt1]
                for nt1 in grammar for nt2 in grammar
            )

            if condition_1 or condition_2 or condition_3:
                bigram_matrix[y1].add(y2)

    return bigram_matrix


def generate_string(bigramms, terminals, first, start, randomness_prob):
    result = random.choice(list(first[start]))
    last_symb = result

    while bigramms[last_symb]:
        rand = random.random()
        if rand > 0.1:
            if rand < randomness_prob:
                # С вероятностью добавляем случайный терминал
                last_symb = random.choice(list(terminals))
                result += last_symb
            else:
                # В противном случае добавляем символ на основе биграмм, если они доступны
                if last_symb in bigramms and bigramms[last_symb]:
                    last_symb = random.choice(list(bigramms[result[-1]]))
                    result += last_symb
                else:
                    # Если биграмм для текущего символа нет, завершаем генерацию
                    break
        else:
            break

    return result


def cyk(grammar, start_symbol, string):
    n = len(string)
    if n == 0:
        return False

    # Таблица CYK
    dp = [[set() for _ in range(n)] for _ in range(n)]

    # Заполняем базовый случай (однобуквенные правила)
    for i, char in enumerate(string):
        for nonterminal, productions in grammar.items():
            for production in productions:
                if production == [char]:
                    dp[i][i].add(nonterminal)

    # Заполняем таблицу для подстрок длиной от 2 до n
    for length in range(2, n + 1):
        for i in range(n - length + 1):
            j = i + length - 1
            for k in range(i, j):
                for nonterminal, productions in grammar.items():
                    for production in productions:
                        if len(production) == 2:
                            B, C = production
                            if B in dp[i][k] and C in dp[k + 1][j]:
                                dp[i][j].add(nonterminal)

    # Проверяем, порождает ли стартовый символ строку
    return start_symbol in dp[0][n - 1]


grammar_file = "grammar.txt"
lines = read_grammar_from_file(grammar_file)

grammar = parse(lines)
start = 'S'

cnf_grammar = convert_to_cnf(grammar, start)
print("Исходная грамматика в ХНФ:")
my_print(cnf_grammar)

first = build_first(cnf_grammar)
follow = build_follow(cnf_grammar, first)
precede = build_precede(cnf_grammar, first)
last = build_last(cnf_grammar)

terminals = extract_terminals(cnf_grammar)
bigramms = build_bigramms(grammar, terminals, first, follow, last, precede)

test_count = 30
randomness_prob = 0.2
test_results = generate_and_test(cnf_grammar, terminals, first, test_count, start, randomness_prob)

test_results_file = "test_results.txt"
write_test_results(test_results_file, test_results)

example_string = "a"
test_string(example_string, cnf_grammar, start)
