const proofSteps = (state = [], action) => {

  switch (action.type) {

    case 'RECEIVE_CHECK_STATUS':
      if (action.valid) {
        return [
          ...state,
          {
            derived: action.id,
            justification: action.justification
          }
        ]
      }

      return state

    default:
      return state
  }
}

export default proofSteps

