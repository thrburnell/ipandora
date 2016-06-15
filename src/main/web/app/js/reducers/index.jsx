import { combineReducers } from 'redux'
import mode from './Mode'
import toShow from './ToShow'
import proof from './Proof'
import given from './Given'

const ipandoraApp = combineReducers({
  mode,
  toShow,
  proof,
  given
})

export default ipandoraApp

