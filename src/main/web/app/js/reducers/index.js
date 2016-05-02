import { combineReducers } from 'redux'
import knownFormulas from './knownformulas'
import givens from './givens'
import toShows from './toshows'
import proofSteps from './proofsteps'

const ipandoraApp = combineReducers({
  knownFormulas,
  givens,
  toShows,
  proofSteps
})

export default ipandoraApp

