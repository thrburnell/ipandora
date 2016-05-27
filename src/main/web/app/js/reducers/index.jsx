import { combineReducers } from 'redux'
import fn from './Fn'
import prototypes from './Prototypes'
import toShow from './ToShow'
import baseCase from './BaseCase'
import inductiveCase from './InductiveCase'

const ipandoraApp = combineReducers({
  fn,
  prototypes,
  toShow,
  baseCase,
  inductiveCase
})

export default ipandoraApp

