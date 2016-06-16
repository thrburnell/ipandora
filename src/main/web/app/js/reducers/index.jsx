import { combineReducers } from 'redux'
import {reducer as formReducer} from 'redux-form';
import { SAVE_GIVEN_INDEX } from '../actions'
import mode from './Mode'
import toShow from './ToShow'
import proof from './Proof'
import given from './Given'
import givenEntryComplete from './GivenEntryComplete'

const ipandoraApp = combineReducers({
  mode,
  toShow,
  proof,
  given,
  givenEntryComplete,
  form: formReducer
})

export default ipandoraApp

