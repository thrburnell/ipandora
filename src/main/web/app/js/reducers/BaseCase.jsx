import { RECEIVE_INDUCTION_SCHEMA } from '../actions'

const BaseCase = (state={}, action) => {

  switch (action.type) {
    case RECEIVE_INDUCTION_SCHEMA:
      return action.baseCase
    default:
      return state
  }

}

export default BaseCase

