import flask as FL
from flask import Flask
import syntax as S
from syntax import F, V

@S.mixfix
class Top:
  s: S.Str('1')
S.prec_top(Top)
S.prec_top(Top.s)

@S.mixfix
class Times:
  p: any
  times: S.Str('*', tex=r'\times ')
  q: any
S.prec_ge(Times, Times.times) # right associative

@S.mixfix
class Plus:
  p: any
  plus: S.Str('+')
  q: any
S.prec_ge(Plus, Plus.plus) # right associative
S.prec_ges([(Times, Plus), (Times.q, Plus.p), (Times.q, Plus.q)]) # * takes precedence over +

@S.mixfix
class Pow:
  p: any
  to: S.Str('->', tex=r'\to ')
  q: any
S.prec_ge(Pow, Pow.to) # right associative
S.prec_ges([(Plus, Pow), (Plus.q, Pow.p), (Plus, Pow.to), (Plus.q, Pow.q)]) # + takes precedence over ->
# Note: by transitivity, also get that * takes precedence over ->.

@S.mixfix
class Lam:
  lam: S.Str('\\', tex=r'\lambda ')
  m: F
@S.mixfix
class App:
  m: any
  app: S.Str(' ', tex='~')
  n: any
S.prec_ge(App.n, App.m) # left-associative
S.prec_ge(App.n, Lam.m) # application binds stronger than λ

class Stuck(Exception): pass
def step(m):
  match m:
    case Lam(F([x, m])): return Lam(F(x, step(m)))
    case App(Lam(F([x, m])), n): return m.subst({x: n})
    case App(m, n):
      try: return App(step(m), n)
      except Stuck: return App(m, step(n))
    case V(x): raise Stuck()
    case _: raise ValueError(f'step({m})')

def trace(m, bound=10):
  res = [m]
  for _ in range(bound):
    try: res.append(step(res[-1]))
    except Stuck: break
  return res

# ----------

def base64image(path):
  import base64
  with open(path, 'rb') as f:
    bytes = f.read()
  return base64.b64encode(bytes).decode('utf-8')

def img(path):
  return f'<img src="data:image/png;base64,{base64image(path)}"></img>'

app = Flask(__name__)   

@app.route('/', methods = ['GET'])
def main():
  return FL.render_template('index.html')

@app.route('/input', methods = ['POST'])
def on_input():
  import html as H
  s = H.unescape(FL.request.data.decode('utf-8'))
  if s.endswith('<br>'): s = s[:-len('<br>')]
  print('Received input:', s)
  try:
    m = S.global_parser.parse(s)
    steps = [n.simple_names().str("tex") for n in trace(m, bound=800)]
    str_steps = '\\longrightarrow '.join(steps[-1:])
    return f'$\\displaystyle \\cdots \\stackrel{{{len(steps)-1}}}\\longrightarrow {str_steps}$'
  except Exception as e:
    return H.escape(str(e)) + '<br>' + img('serverok.png')

if __name__ == '__main__':
  app.run()