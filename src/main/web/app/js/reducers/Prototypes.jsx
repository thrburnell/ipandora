import { RECEIVE_FUNCTION_VALIDITY } from '../actions'

const Prototypes = (state=[], action) => {
  switch (action.type) {
    case RECEIVE_FUNCTION_VALIDITY:
      if (action.valid) {
        return [
          ...state,
          action.prototype
        ]
      }
    default:
      return state
  }
}

export default Prototypes

