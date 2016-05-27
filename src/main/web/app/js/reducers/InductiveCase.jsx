import { RECEIVE_INDUCTION_SCHEMA } from '../actions'

const InductiveCase = (state={}, action) => {

  switch (action.type) {
    case RECEIVE_INDUCTION_SCHEMA:
      return action.inductiveCase
    default:
      return state
  }

}

export default InductiveCase

