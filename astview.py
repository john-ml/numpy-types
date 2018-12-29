import ast
import npcheck.pattern as P

while True:
    try:
        s = input('> ').split('<==')
        if len(s) == 1:
            print(P.pretty(P.explode(ast.parse(s[0]))))
        else:
            lhs, rhs = s[0], s[1]
            print(P.pretty_matches(
                P.matches(P.raw_pattern(lhs), ast.parse(rhs.lstrip()))))
    except KeyboardInterrupt:
        exit()
    except Exception as e:
        print(e)
