def expect(want, have):
  if want != have:
    raise Exception(f'\nWant: {want}\nHave: {have}')
def raises(thunk):
  try:
    v = thunk()
    raise ValueError(f'Instead of exception got {v}')
  except: pass