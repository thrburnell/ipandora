import { connect } from 'react-redux'
import { getInductionSchema } from '../actions'
import ToShow from '../components/ToShow'

const mapStateToProps = (state) => (
  {
    ...state.toShow,
    active: state.fn.valid
  }
)

const mapDispatchToProps = (dispatch) => (
  {
    onValidateClick: (formula, variable) => dispatch(getInductionSchema(formula, variable))
  }
)

const RToShow = connect(
  mapStateToProps,
  mapDispatchToProps
)(ToShow)

export default RToShow

