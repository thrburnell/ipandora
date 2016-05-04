const proofStepJustification = (state = [], action) => {
  switch (action.type) {
    case 'SELECT_JUSTIFICATION':
      // If already selected, remove
      if (state.findIndex(e => e == action.id) >= 0) {
        return state.filter(e => e != action.id)
      }

      return  [
        ...state,
        action.id
      ]

    case 'RECEIVE_CHECK_STATUS':
      return action.valid ? [] : state

    default:
      return state
  }
}

export default proofStepJustification

