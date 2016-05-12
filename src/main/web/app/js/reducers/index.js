import { combineReducers } from 'redux'
import knownFormulas from './knownformulas'
import givens from './givens'
import toShows from './toshows'
import proofSteps from './proofsteps'
import proofStepJustification from './proofstepjustification'

const ipandoraApp = combineReducers({
  knownFormulas,
  givens,
  toShows,
  proofSteps,
  proofStepJustification
})

export default ipandoraApp

