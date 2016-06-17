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
import arbitrary from './Arbitrary'
import proofComplete from './ProofComplete'

const ipandoraApp = combineReducers({
  mode,
  toShow,
  proof,
  given,
  givenEntryComplete,
  proofStepType,
  selectedLines,
  arbitrary,
  proofComplete,
  form: formReducer
})

export default ipandoraApp

