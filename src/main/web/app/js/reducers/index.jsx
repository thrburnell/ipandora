import { combineReducers } from 'redux'
import {reducer as formReducer} from 'redux-form';
import { SAVE_GIVEN_INDEX } from '../actions'
import mode from './Mode'
import toShow from './ToShow'
import proof from './Proof'
import given from './Given'
import givenEntryComplete from './GivenEntryComplete'
import proofStepType from './ProofStepType'
import selectedLines from './SelectedLines'

const ipandoraApp = combineReducers({
  mode,
  toShow,
  proof,
  given,
  givenEntryComplete,
  proofStepType,
  selectedLines,
  form: formReducer
})

export default ipandoraApp

