import { combineReducers } from 'redux'
import fn from './Fn'
import toShow from './ToShow'
import baseCase from './BaseCase'
import inductiveCase from './InductiveCase'

const ipandoraApp = combineReducers({
  fn,
  toShow,
  baseCase,
  inductiveCase
})

export default ipandoraApp

